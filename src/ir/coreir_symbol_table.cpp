#include "coreir/ir/coreir_symbol_table.hpp"
#include <set>
#include <utility>
#include "coreir/common/logging_lite.hpp"

namespace CoreIR {

namespace {

using json_type = ::nlohmann::json;
using InstanceNameType = SymbolTableInterface::InstanceNameType;
using StringPair = std::array<std::string, 2>;
using StringTriple = std::array<std::string, 3>;

template <typename Key, typename Value> struct Jsonifier {
  using map_type = std::map<Key, Value>;

  json_type operator()(const map_type& map) const {
    return json_type(map);
  }
};

template <typename CollectionType> std::string joinStrings(
    const CollectionType& collection, std::string seperator = ",") {
  if (collection.size() == 0) return "";
  auto joined = collection[0];
  const auto bound = static_cast<int>(collection.size());
  for (int i = 1; i < bound; i++) {
    joined += (seperator + collection[i]);
  }
  return joined;
}

template <std::size_t N>
struct Jsonifier<std::array<std::string, N>, std::string> {
  using Key = std::array<std::string, N>;
  using Value = std::string;
  using map_type = std::map<Key, Value>;

  json_type operator()(const map_type& map) const {
    std::map<std::string, std::string> transformed;
    for (auto& [k, v] : map) {
      auto new_key = joinStrings(k);
      transformed[new_key] = v;
    }
    return Jsonifier<std::string, std::string>()(transformed);
  }
};

template <std::size_t N>
struct Jsonifier<std::array<std::string, N>, InstanceNameType> {
  using Key = std::array<std::string, N>;
  using Value = InstanceNameType;
  using map_type = std::map<Key, Value>;

  json_type operator()(const map_type& map) const {
    std::map<std::string, std::array<std::string, 2>> transformed;
    for (auto& [k, v] : map) {
      auto new_key = joinStrings(k);
      transformed[new_key] = {std::get<0>(v)->getFlag(), std::get<1>(v)};
    }
    return Jsonifier<std::string, std::array<std::string, 2>>()(transformed);
  }
};

class LoggerImpl : public SymbolTableLoggerInterface {
 public:
  LoggerImpl(SymbolTableInterface* table) : SymbolTableLoggerInterface(table) {}
  ~LoggerImpl() = default;

  void logNewInstance(
      std::string module_name,
      std::string instance_type,
      std::string instance_name) override {
    const std::vector data {module_name, instance_type, instance_name};
    logGeneral(LogKind::NEW, data);
  }

  void logRemoveInstance(
      std::string module_name, std::string instance_name) override {
    const std::vector data {module_name, instance_name};
    logGeneral(LogKind::REMOVE, data);
  }

  void logRenameInstance(
      std::string module_name,
      std::string instance_name,
      std::string new_instance_name) override {
    const std::vector data {module_name, instance_name, new_instance_name};
    logGeneral(LogKind::RENAME, data);
  }

  void logInlineInstance(
      std::string module_name,
      std::string instance_name,
      std::string instance_type,
      std::string child_instance_name,
      std::string child_instance_type,
      std::string new_instance_name) override {
    const std::vector data {
      module_name,
      instance_name,
      instance_type,
      child_instance_name,
      child_instance_type,
      new_instance_name
    };
    logGeneral(LogKind::INLINE, data);
  }

  void pauseLogging() override { paused = true; }
  void resumeLogging() override { paused = false; }

  bool finalize() override {
    std::string error;
    if (not finalizeImpl(&error)) {
      LOG(DEBUG) << "finalize failed: " << error;
      assert(false);
    }
    return true;
  }

  std::unique_ptr<SymbolTableLoggerInterface::DebugIterator>
  debugIterator() const override {
    return std::make_unique<DebugIterator>(log);
  }

 private:
  enum LogKind {
    NEW = 0,
    REMOVE,
    RENAME,
    INLINE
  };
  using LogDataType = std::vector<std::string>;
  using EntryType = std::pair<LogKind, LogDataType>;

  static std::string entryToString(EntryType entry) {
    static const char* kind_strings[] = {"NEW", "REMOVE", "RENAME", "INLINE"};
    return std::string(kind_strings[entry.first]) + " "
        + joinStrings(entry.second, " ");
  }

  class DebugIterator : public SymbolTableLoggerInterface::DebugIterator {
   public:
    explicit DebugIterator(const std::vector<EntryType>& log)
        : current(log.begin() - 1), end(log.end()) {}
    ~DebugIterator() = default;

    bool next() override { return (++current) != end; }
    std::string debugString() const override { return entryToString(*current); }

   private:
    std::vector<EntryType>::const_iterator current;
    std::vector<EntryType>::const_iterator end;
  };

  void logGeneral(LogKind kind, LogDataType data) {
    if (paused) return;
    log.emplace_back(kind, data);
  }

  bool finalizeImpl(std::string* err) {
    struct InstanceInfo;
    struct ModuleInfo {
      const std::string name;
      std::map<std::string, std::unique_ptr<InstanceInfo>> instances = {};

      InstanceInfo* tryGetInstance(std::string name) const {
        try {
          return instances.at(name).get();
        } catch (std::out_of_range&) {
          return nullptr;
        }
      }

      std::string DebugString() const { return "Module(" + name + ")"; }
    };
    struct InstanceInfo {
      const std::string name;
      const ModuleInfo* const type;
      bool removed = false;
      bool inlined = false;
      bool from_inline = false;
      std::vector<std::array<InstanceInfo*, 2>> inlines = {};
      std::tuple<ModuleInfo*, InstanceInfo*, InstanceInfo*> inline_source = {};

      std::string DebugString() const {
        assert(removed == inlined);
        auto s = "Instance(" + name + ", type=" + type->name;
        if (from_inline) {
          s += ", from_inline=True";
        }
        if (inlined) {
          std::vector<std::string> inline_strs;
          for (const auto& ii : inlines) {
            inline_strs.push_back("(" + ii[0]->name + ", " + ii[1]->name + ")");
          }
          s += ", inlines=[" + joinStrings(inline_strs) + "]";
        }
        s += ")";
        return s;
      }
    };
    std::map<std::string, std::unique_ptr<ModuleInfo>> modules;
    auto add_or_get_module = [&modules](std::string name) {
      auto it = modules.find(name);
      if (it != modules.end()) return it->second.get();
      std::unique_ptr<ModuleInfo> module(new ModuleInfo {name});
      auto ret = modules.emplace(name, module.release());
      assert(ret.second);
      return ret.first->second.get();
    };
    auto get_module = [&modules](std::string name) {
      try {
        return modules.at(name).get();
      } catch (std::out_of_range&) {
        return static_cast<ModuleInfo*>(nullptr);
      }
    };
    for (auto it = log.cbegin(); it != log.cend(); it++) {
      const auto& [kind, data] = *it;
      *err = entryToString(*it);  // pre-emptively set the error string
      switch (kind) {
        case NEW: {
          const auto& module_name = data[0];
          const auto& instance_type = data[1];
          const auto& instance_name = data[2];
          auto module = add_or_get_module(module_name);
          auto type = add_or_get_module(instance_type);
          auto ret = module->instances.emplace(
              instance_name, new InstanceInfo {instance_name, type});
          if (not ret.second) return false;
          break;
        }
        case REMOVE: {
          const auto& module_name = data[0];
          const auto& instance_name = data[1];
          auto module = get_module(module_name);
          if (module == nullptr) return false;
          auto inst = module->tryGetInstance(instance_name);
          if (inst == nullptr) return false;
          if (inst->removed) return false;
          inst->removed = true;
          break;
        }
        case INLINE: {
          const auto& module_name = data[0];
          const auto& parent_instance_name = data[1];
          const auto& child_instance_name = data[3];
          const auto& new_instance_name = data[5];
          auto module = get_module(module_name);
          if (module == nullptr) return false;
          auto parent_inst = module->tryGetInstance(parent_instance_name);
          if (parent_inst == nullptr) return false;
          if (not parent_inst->removed) return false;
          parent_inst->inlined = true;
          auto new_inst = module->tryGetInstance(new_instance_name);
          if (new_inst == nullptr
              or new_inst->removed
              or new_inst->inlined
              or new_inst->from_inline) {
            return false;
          }
          new_inst->from_inline = true;
          auto child_inst = parent_inst->type->tryGetInstance(
              child_instance_name);
          if (child_inst == nullptr) return false;
          new_inst->inline_source = {module, parent_inst, child_inst};
          parent_inst->inlines.push_back(std::array {child_inst, new_inst});
          break;
        }
        default: {
          assert(false);
        }
      }
    }
    int uniq_index = 0;
    auto make_uniq_key = [&uniq_index] () {
      return "UNIQ_KEY_" + std::to_string(uniq_index++);
    };
    class TableWrapper {
     public:
      explicit TableWrapper(SymbolTableInterface* table) : table(table) {}

      void setType(
          std::string module_name,
          std::string inst_name,
          std::string type_name) {
        LOG(DEBUG) << "T(" << module_name << ", " << inst_name << ") -> "
                   << type_name;
        table->setInstanceType(module_name, inst_name, type_name);
      }
      void setName(
          std::string module_name,
          std::string inst_name,
          std::string out_inst_name) {
        const auto sentinel = symbolTableEmptySentinel();
        LOG(DEBUG) << "P(" << module_name << ", " << inst_name << ") -> "
                   << "(" << sentinel->getFlag() << ", "
                   << out_inst_name << ")";
        auto out = std::tuple {sentinel, out_inst_name};
        table->setInstanceName(module_name, inst_name, out);
      }
      void setNameInlined(std::string module_name, std::string inst_name) {
        const auto sentinel = symbolTableInlinedInstanceSentinel();
        LOG(DEBUG) << "P(" << module_name << ", " << inst_name << ") -> "
                   << "(" << sentinel->getFlag() << ", " << "" << ")";
        auto out = std::tuple {sentinel, std::string("")};
        table->setInstanceName(module_name, inst_name, out);
      }
      void setInlineName(
          std::string module_name,
          std::string parent_inst_name,
          std::string child_inst_name,
          std::string new_name) {
        const auto sentinel = symbolTableEmptySentinel();
        LOG(DEBUG) << "S(" << module_name << ", " << parent_inst_name << ", "
                   << child_inst_name << ") -> " << "(" << sentinel->getFlag()
                   << ", " << new_name << ")";
        auto out = std::tuple {sentinel, new_name};
        table->setInlinedInstanceName(
            module_name, parent_inst_name, child_inst_name, out);
      }
      void setInlineNameInlined(
          std::string module_name,
          std::string parent_inst_name,
          std::string child_inst_name,
          std::string key) {
        const auto sentinel = symbolTableInlinedInstanceSentinel();
        LOG(DEBUG) << "S(" << module_name << ", " << parent_inst_name << ", "
                   << child_inst_name << ") -> " << "(" << sentinel->getFlag()
                   << ", " << key << ")";
        auto out = std::tuple {sentinel, key};
        table->setInlinedInstanceName(
            module_name, parent_inst_name, child_inst_name, out);
      }

     private:
      SymbolTableInterface* const table;
    };
    TableWrapper wrapper(table);
    // NOTE(rsetaluri): These lambdas need to be declared up-front since they
    // are mutually recursive.
    std::function<void(ModuleInfo* const, InstanceInfo* const)> handler;
    std::function<void(ModuleInfo* const,
                       InstanceInfo* const,
                       std::string)> inline_handler;
    handler = [&inline_handler, &wrapper](auto module, auto inst) {
      if (inst->from_inline) return;
      assert(inst->inlined or inst->inlines.size() == 0);
      wrapper.setType(module->name, inst->name, inst->type->name);
      if (not inst->inlined) {
        wrapper.setName(module->name, inst->name, inst->name);
        return;
      }
      wrapper.setNameInlined(module->name, inst->name);
      inline_handler(module, inst, "");
    };
    inline_handler = [&inline_handler, &make_uniq_key, &wrapper](
        auto module, auto inst, auto key) {
      auto key_or_inst_name = (key == "") ? inst->name : key;
      for (const auto& inline_info : inst->inlines) {
        const auto& [src, dst] = std::tuple {inline_info[0], inline_info[1]};
        assert(not (dst->inlined and src->from_inline));
        if (dst->inlined) {  // top-down case
          assert(inst->from_inline == (key != ""));
          auto new_key = make_uniq_key();
          wrapper.setInlineNameInlined(
              module->name, key_or_inst_name, src->name, new_key);
          inline_handler(module, dst, new_key);
        } else if (src->from_inline) {  // bottom-up case
          auto curr_src = src;
          auto curr_key = key_or_inst_name;
          while (curr_src->from_inline) {
            auto new_key = make_uniq_key();
            auto child_name = std::get<1>(curr_src->inline_source)->name;
            wrapper.setInlineNameInlined(
                module->name, curr_key, child_name, new_key);
            curr_src = std::get<2>(curr_src->inline_source);
            curr_key = new_key;
          }
          assert(not curr_src->from_inline);
          wrapper.setInlineName(
              module->name, curr_key, curr_src->name, dst->name);
        } else {
          wrapper.setInlineName(
              module->name, key_or_inst_name, src->name, dst->name);
        }
      }
    };
    for (const auto& item : modules) {
      const auto& module = item.second;
      LOG(DEBUG) << module->DebugString();
      for (const auto& inst_item : module->instances) {
        const auto& inst = inst_item.second;
        LOG(DEBUG) << "    " << inst->DebugString();
        handler(module.get(), inst.get());
      }
    }
    return true;
  }

  std::vector<EntryType> log;
  bool paused = false;
};

}  // namespace

SymbolTableSentinel* const symbolTableInlinedInstanceSentinel() {
  static SymbolTableSentinel sentinel("__SYMBOL_TABLE_INLINED_INSTANCE__");
  return &sentinel;
}

SymbolTableSentinel* const symbolTableEmptySentinel() {
  static SymbolTableSentinel sentinel("__SYMBOL_TABLE_EMPTY__");
  return &sentinel;
}

CoreIRSymbolTable::CoreIRSymbolTable()
    : logger(new LoggerImpl(this)) {}

void CoreIRSymbolTable::setModuleName(
    std::string in_module_name, std::string out_module_name) {
  moduleNames.emplace(in_module_name, out_module_name);
}

void CoreIRSymbolTable::setInstanceName(
    std::string in_module_name,
    std::string in_instance_name,
    InstanceNameType out_instance_name) {
  std::array key = {in_module_name, in_instance_name};
  instanceNames.emplace(key, out_instance_name);
}

void CoreIRSymbolTable::setPortName(
    std::string in_module_name,
    std::string in_port_name,
    std::string out_port_name) {
  std::array key = {in_module_name, in_port_name};
  portNames.emplace(key, out_port_name);
}

void CoreIRSymbolTable::setInlinedInstanceName(
      std::string in_module_name,
      std::string in_parent_instance_name,
      std::string in_child_instance_name,
      InstanceNameType out_instance_name) {
  std::array key = {
    in_module_name, in_parent_instance_name, in_child_instance_name};
  inlinedInstanceNames.emplace(key, out_instance_name);
}

void CoreIRSymbolTable::setInstanceType(
      std::string in_module_name,
      std::string in_instance_name,
      std::string out_type) {
  std::array key = {in_module_name, in_instance_name};
  instanceTypes.emplace(key, out_type);
}

std::string CoreIRSymbolTable::getModuleName(std::string in_module_name) const {
  return moduleNames.at(in_module_name);
}

InstanceNameType CoreIRSymbolTable::getInstanceName(
    std::string in_module_name, std::string in_instance_name) const {
  return instanceNames.at({in_module_name, in_instance_name});
}

std::string CoreIRSymbolTable::getPortName(
    std::string in_module_name, std::string in_port_name) const {
  return portNames.at({in_module_name, in_port_name});
}

InstanceNameType CoreIRSymbolTable::getInlinedInstanceName(
    std::string in_module_name,
    std::string in_parent_instance_name,
    std::string in_child_instance_name) const {
  return inlinedInstanceNames.at(
      {in_module_name, in_parent_instance_name, in_child_instance_name});
}

std::string CoreIRSymbolTable::getInstanceType(
    std::string in_module_name, std::string in_instance_name) const {
  return instanceTypes.at({in_module_name, in_instance_name});
}

json_type CoreIRSymbolTable::json() const {
  json_type ret;
  ret["module_names"] = Jsonifier<std::string, std::string>()(moduleNames);
  ret["instance_names"] = Jsonifier<StringPair, InstanceNameType>()(
      instanceNames);
  ret["port_names"] = Jsonifier<StringPair, std::string>()(portNames);
  ret["inlined_instance_names"] = Jsonifier<StringTriple, InstanceNameType>()(
      inlinedInstanceNames);
  ret["instance_types"] = Jsonifier<StringPair, std::string>()(instanceTypes);
  return ret;
}

}  // namespace CoreIR
