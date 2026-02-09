// WASM Bridge: C++23 → React Runtime (Complete Implementation)
#include <emscripten.h>
#include <emscripten/bind.h>
#include <emscripten/val.h>
#include <string>
#include <vector>
#include <functional>
#include <memory>
#include <map>
#include <unordered_map>

using namespace emscripten;

// React component props (complete)
struct ReactProps {
    std::string className;
    std::map<std::string, std::string> attributes;
    std::vector<std::string> children;
    std::map<std::string, val> callbacks;  // Event handlers
    std::map<std::string, val> refs;       // React refs
};

// React component return value
struct ReactElement {
    std::string type;
    ReactProps props;
    std::vector<ReactElement> children;
    std::string key;  // React key
    bool isFragment = false;
};

// Component factory type
using ComponentFactory = std::function<ReactElement(const ReactProps&)>;

// Component registry with lifecycle management
class ComponentRegistry {
public:
    void register_component(const std::string& name, ComponentFactory factory) {
        components_[name] = factory;
    }
    
    void unregister_component(const std::string& name) {
        components_.erase(name);
    }
    
    ReactElement create_component(const std::string& name, const ReactProps& props) {
        auto it = components_.find(name);
        if (it != components_.end()) {
            try {
                return it->second(props);
            } catch (const std::exception& e) {
                // Return error element
                return create_error_element(std::string("Component error: ") + e.what());
            }
        }
        return create_error_element("Component not found: " + name);
    }
    
    bool has_component(const std::string& name) const {
        return components_.find(name) != components_.end();
    }
    
    std::vector<std::string> list_components() const {
        std::vector<std::string> names;
        for (const auto& [name, _] : components_) {
            names.push_back(name);
        }
        return names;
    }
    
private:
    std::unordered_map<std::string, ComponentFactory> components_;
    
    ReactElement create_error_element(const std::string& message) {
        ReactProps props;
        props.attributes["data-error"] = message;
        props.className = "error-component";
        return ReactElement{"div", props, {}};
    }
};

static ComponentRegistry g_registry;

// React element creation helpers
ReactElement create_element(const std::string& type, 
                           const ReactProps& props,
                           const std::vector<ReactElement>& children) {
    return ReactElement{type, props, children};
}

ReactElement create_fragment(const std::vector<ReactElement>& children) {
    ReactElement elem;
    elem.isFragment = true;
    elem.children = children;
    return elem;
}

ReactElement create_text_element(const std::string& text) {
    ReactProps props;
    props.attributes["textContent"] = text;
    return ReactElement{"#text", props, {}};
}

ReactElement create_portal(const ReactElement& element, const std::string& container_id) {
    ReactProps props = element.props;
    props.attributes["data-portal"] = container_id;
    return ReactElement{"portal", props, element.children};
}

// Export component registration
EMSCRIPTEN_KEEPALIVE
void register_cpp_component(const std::string& name, ComponentFactory factory) {
    g_registry.register_component(name, factory);
}

// Export component creation
EMSCRIPTEN_KEEPALIVE
ReactElement create_cpp_component(const std::string& name, const ReactProps& props) {
    return g_registry.create_component(name, props);
}

// Export component check
EMSCRIPTEN_KEEPALIVE
bool has_cpp_component(const std::string& name) {
    return g_registry.has_component(name);
}

// Export component list
EMSCRIPTEN_KEEPALIVE
std::vector<std::string> list_cpp_components() {
    return g_registry.list_components();
}

// Export component unregistration
EMSCRIPTEN_KEEPALIVE
void unregister_cpp_component(const std::string& name) {
    g_registry.unregister_component(name);
}

// Bind to JavaScript with complete API
EMSCRIPTEN_BINDINGS(react_bridge) {
    class_<ReactProps>("ReactProps")
        .property("className", &ReactProps::className)
        .property("attributes", &ReactProps::attributes)
        .property("children", &ReactProps::children)
        .property("callbacks", &ReactProps::callbacks)
        .property("refs", &ReactProps::refs);
    
    class_<ReactElement>("ReactElement")
        .property("type", &ReactElement::type)
        .property("props", &ReactElement::props)
        .property("children", &ReactElement::children)
        .property("key", &ReactElement::key)
        .property("isFragment", &ReactElement::isFragment);
    
    function("registerCppComponent", &register_cpp_component);
    function("createCppComponent", &create_cpp_component);
    function("hasCppComponent", &has_cpp_component);
    function("listCppComponents", &list_cpp_components);
    function("unregisterCppComponent", &unregister_cpp_component);
    function("createElement", &create_element);
    function("createFragment", &create_fragment);
    function("createTextElement", &create_text_element);
    function("createPortal", &create_portal);
    
    register_vector<std::string>("StringVector");
    register_map<std::string, std::string>("StringMap");
    register_map<std::string, val>("StringValMap");
}
