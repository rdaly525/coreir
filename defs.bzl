load("@bazel_skylib//lib:paths.bzl", "paths")

# TODO(rsetaluri): Move this in a separate template file.
_INSTALL_SCRIPT_TPL = """
RED="\033[0;31m"
GREEN="\033[0;32m"
NC="\033[0m"

function main() {{
  local src="$1"
  local dst="$2"
  PATH_="$DIRECTORY/{subdirectory}/"
  DIR=`dirname ${{PATH_}}${{dst}}`
  if [ ! -z "$SUDO" ]; then
    if [ $MKDIR != "0" ]; then
      ERR=$(sudo mkdir -p ${{DIR}})
    fi
    ERR=$(sudo cp -p ${{src}} ${{PATH_}}${{dst}} 2>&1 > /dev/null)
  else
    if [ $MKDIR != "0" ]; then
      ERR=$(mkdir -p ${{DIR}})
    fi
    ERR=$(cp -p ${{src}} ${{PATH_}}${{dst}} 2>&1 > /dev/null)
  fi
  RES=$?
  ACTION="${{src}} to ${{PATH_}}${{dst}}"
  if [ $RES == "0" ]; then
      MSG="Installed ${{ACTION}}"
      printf "${{GREEN}}${{MSG}}${{NC}}\n"
  else
      MSG="Installation of ${{ACTION}} failed:\n${{ERR}}"
      >&2 echo "${{RED}}${{MSG}}${{NC}}"
      MSG="Perhaps directory ${{PATH_}} needs to be created, or use -s for sudo"
      >&2 echo "${{RED}}${{MSG}}${{NC}}"
  fi
}}

function usage() {{
  >&2 echo "Usage: bazel run {target} [-c opt] -- [-h] [-s] DESTINATION"
}}

function bad_option() {{
  >&2 echo "${{RED}}Unexpected option '-$1'${{NC}}"
  usage
  exit 1
}}

function parse() {{
  while getopts ':sh' flag; do
    case "${{flag}}" in
      s) SUDO="1" ;;
      h) usage; exit 0 ;;
      *) bad_option ${{OPTARG}} ;;
    esac
  done
  if [[ -z "${{OPTIND:-}}" ]] || (($OPTIND > $#)); then
    DIRECTORY={default_directory}
  else
    DIRECTORY="${{!OPTIND}}"
  fi
}}

parse "$@"
SRCS=({srcs})
DSTS=({dsts})
MKDIR={mkdir}
for i in {{0..{loop_bound}}}; do
  main ${{SRCS[$i]}} ${{DSTS[$i]}}
done
"""


def _install_helper(ctx, try_get_srcs, mkdir=False):
    srcs, dsts, err = try_get_srcs(ctx)
    if err != None:
        fail(err)
    if len(srcs) == 0 or len(srcs) != len(dsts):
        msg = "Expected srcs and dsts to be the same length; got {} and {}"
        fail(msg.format(str(srcs), str(dsts)))
    installer = ctx.outputs.installer
    content = _INSTALL_SCRIPT_TPL.format(
        target = ctx.label,
        srcs = " ".join([src.short_path for src in srcs]),
        dsts = " ".join(dsts),
        subdirectory = ctx.attr.subdirectory,
        default_directory = ctx.attr.default_directory,
        loop_bound = len(srcs) - 1,
        mkdir = "1" if mkdir else "0"
    )
    ctx.actions.write(
        output = installer,
        content = content,
        is_executable = True
    )
    runfiles = ctx.runfiles(
        files = [installer] + srcs
    )
    provider = DefaultInfo(
        executable = installer,
        runfiles = runfiles
    )
    return [provider]


def _try_get_lib(ctx):
    libs = ctx.attr.lib.output_groups.dynamic_library.to_list()
    if len(libs) != 1:
        err = "Expected exactly one library; got {}".format(len(libs))
        return None, None, err
    lib = libs[0]
    dst = lib.basename if ctx.attr.rename == "" else ctx.attr.rename
    return [lib], [dst], None


def _install_lib_impl(ctx):
    return _install_helper(ctx, _try_get_lib)


def _try_get_bin(ctx):
    bins = ctx.attr.bin.files.to_list()
    if len(bins) != 1:
        err = "Expected exactly one binary; got {}".format(len(bins))
        return None, None, err
    bin = bins[0]
    dst = bin.basename if ctx.attr.rename == "" else ctx.attr.rename
    return [bin], [dst], None


def _install_bin_impl(ctx):
    return _install_helper(ctx, _try_get_bin)


def _try_get_hdrs(ctx):
    actions = ctx.attr.hdrs.actions
    hdrs = []
    for action in actions:
        for inp in action.inputs.to_list():
            if not inp.is_source:
                continue
            hdrs += [inp]
    if len(hdrs) == 0:
        err = "Expected at least one header file; got 0"
        return None, None, err
    dsts = [hdr.basename for hdr in hdrs]
    return hdrs, dsts, None


def _install_hdrs_impl(ctx):
    return _install_helper(ctx, _try_get_hdrs, mkdir=True)


def _install_set_impl(ctx):
    master = ctx.outputs.master
    master_deps = []
    executables = []
    for dep in ctx.attr.deps:
        master_deps += (dep.data_runfiles.files.to_list() +
                        dep.default_runfiles.files.to_list() +
                        [dep.files_to_run.executable])
        executables += [dep.files_to_run.executable]
    content = "\n".join(["./{} \"$@\"".format(exe.short_path)
                         for exe in executables])
    content += "\n"
    ctx.actions.write(
        output = master,
        content = content,
        is_executable = True
    )
    runfiles = ctx.runfiles(
        files = [master] + master_deps
    )
    provider = DefaultInfo(
        executable = master,
        runfiles = runfiles
    )
    return [provider]


install_lib = rule(
    implementation = _install_lib_impl,
    executable = True,
    attrs = {
        "lib": attr.label(mandatory = True),
        "default_directory": attr.string(mandatory = True),
        "subdirectory": attr.string(default = ""),
        "rename": attr.string(mandatory = False, default = "")
    },
    outputs = {
        "installer": "%{name}_installer.sh"
    })

install_bin = rule(
    implementation = _install_bin_impl,
    executable = True,
    attrs = {
        "bin": attr.label(mandatory = True),
        "default_directory": attr.string(mandatory = True),
        "subdirectory": attr.string(default = ""),
        "rename": attr.string(mandatory = False, default = "")
    },
    outputs = {
        "installer": "%{name}_installer.sh"
    })

install_hdrs = rule(
    implementation = _install_hdrs_impl,
    executable = True,
    attrs = {
        "hdrs": attr.label(mandatory = True),
        "default_directory": attr.string(mandatory = True),
        "subdirectory": attr.string(default = ""),
    },
    outputs = {
        "installer": "%{name}_installer.sh"
    })


def install_all_hdrs(path, subdirectory, default_directory):
    name = "install_{}_hdrs".format(path.replace("/", "_"))
    basename = path.split("/")[-1]
    hdrs = "//{}:{}_hdrs".format(path, basename)
    subdirectory = "{}/{}".format(subdirectory, path)
    install_hdrs(
        name = name,
        hdrs = hdrs,
        subdirectory = subdirectory,
        default_directory = default_directory)


install_set = rule(
    implementation = _install_set_impl,
    executable = True,
    attrs = {
        "deps": attr.label_list(mandatory = True),
    },
    outputs = {
        "master": "%{name}_master.sh"
    })
