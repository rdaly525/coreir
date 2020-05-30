load("@bazel_tools//tools/build_defs/repo:git.bzl", "new_git_repository")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
all_content = """filegroup(name = "all", srcs = glob(["**"]), visibility = ["//visibility:public"])"""


########################### rules_foreign_cc ###################################
# The below allows us to bring into scope rules for building external libraries
# that use cmake etc. See https://github.com/bazelbuild/rules_foreign_cc.
http_archive(
   name = "rules_foreign_cc",
   strip_prefix = "rules_foreign_cc-master",
   url = "https://github.com/bazelbuild/rules_foreign_cc/archive/master.zip",
)
load("@rules_foreign_cc//:workspace_definitions.bzl", "rules_foreign_cc_dependencies")
rules_foreign_cc_dependencies()
################################################################################


############################# verilogAST #######################################
new_git_repository(
    name = "verilogAST",
    build_file_content = all_content,
    # NOTE(rsetaluri): Use master once this branch is merged.
    branch = "add-full-install",
    remote = "https://github.com/leonardt/verilogAST-cpp"
)
################################################################################
