// Radix UI Component Binder: C++23 → Radix UI Components
// Phase 5: Complete Radix UI Coverage
#include <string>
#include <map>
#include <vector>
#include <set>

namespace radix_binder {

// Complete Radix UI component mapping (all primitives)
static const std::map<std::string, std::string> radix_components = {
    // Core Primitives
    {"Accordion", "@radix-ui/react-accordion"},
    {"AlertDialog", "@radix-ui/react-alert-dialog"},
    {"AspectRatio", "@radix-ui/react-aspect-ratio"},
    {"Avatar", "@radix-ui/react-avatar"},
    {"Checkbox", "@radix-ui/react-checkbox"},
    {"Collapsible", "@radix-ui/react-collapsible"},
    {"ContextMenu", "@radix-ui/react-context-menu"},
    {"Dialog", "@radix-ui/react-dialog"},
    {"DropdownMenu", "@radix-ui/react-dropdown-menu"},
    {"HoverCard", "@radix-ui/react-hover-card"},
    {"Label", "@radix-ui/react-label"},
    {"Menubar", "@radix-ui/react-menubar"},
    {"NavigationMenu", "@radix-ui/react-navigation-menu"},
    {"Popover", "@radix-ui/react-popover"},
    {"Progress", "@radix-ui/react-progress"},
    {"RadioGroup", "@radix-ui/react-radio-group"},
    {"ScrollArea", "@radix-ui/react-scroll-area"},
    {"Select", "@radix-ui/react-select"},
    {"Separator", "@radix-ui/react-separator"},
    {"Slider", "@radix-ui/react-slider"},
    {"Switch", "@radix-ui/react-switch"},
    {"Tabs", "@radix-ui/react-tabs"},
    {"Toast", "@radix-ui/react-toast"},
    {"Toggle", "@radix-ui/react-toggle"},
    {"ToggleGroup", "@radix-ui/react-toggle-group"},
    {"Tooltip", "@radix-ui/react-tooltip"},
    
    // Additional Primitives
    {"Button", "@radix-ui/react-button"},
    {"Card", "@radix-ui/react-card"},
    {"Calendar", "@radix-ui/react-calendar"},
    {"Table", "@radix-ui/react-table"},
    {"Form", "@radix-ui/react-form"},
    {"Portal", "@radix-ui/react-portal"},
    {"Primitive", "@radix-ui/react-primitive"},
    {"Slot", "@radix-ui/react-slot"},
    {"VisuallyHidden", "@radix-ui/react-visually-hidden"},
    {"DirectionProvider", "@radix-ui/react-direction"},
    {"IdProvider", "@radix-ui/react-id"},
    {"RovingFocusGroup", "@radix-ui/react-roving-focus"},
    {"FocusScope", "@radix-ui/react-focus-scope"},
    {"DismissableLayer", "@radix-ui/react-dismissable-layer"},
    {"Collection", "@radix-ui/react-collection"},
    {"Arrow", "@radix-ui/react-arrow"},
    {"Announce", "@radix-ui/react-announce"},
};

// Accessibility attributes mapping
static const std::map<std::string, std::string> accessibility_attrs = {
    {"aria-label", "ariaLabel"},
    {"aria-labelledby", "ariaLabelledBy"},
    {"aria-describedby", "ariaDescribedBy"},
    {"aria-hidden", "ariaHidden"},
    {"aria-expanded", "ariaExpanded"},
    {"aria-selected", "ariaSelected"},
    {"aria-checked", "ariaChecked"},
    {"aria-disabled", "ariaDisabled"},
    {"aria-required", "ariaRequired"},
    {"aria-invalid", "ariaInvalid"},
    {"aria-live", "ariaLive"},
    {"aria-atomic", "ariaAtomic"},
    {"role", "role"},
    {"tabindex", "tabIndex"},
};

// Animation presets
static const std::map<std::string, std::vector<std::string>> animation_presets = {
    {"fade-in", {"animate-in", "fade-in", "duration-200"}},
    {"fade-out", {"animate-out", "fade-out", "duration-200"}},
    {"slide-in-from-top", {"animate-in", "slide-in-from-top", "duration-300"}},
    {"slide-in-from-bottom", {"animate-in", "slide-in-from-bottom", "duration-300"}},
    {"slide-in-from-left", {"animate-in", "slide-in-from-left", "duration-300"}},
    {"slide-in-from-right", {"animate-in", "slide-in-from-right", "duration-300"}},
    {"zoom-in", {"animate-in", "zoom-in", "duration-200"}},
    {"zoom-out", {"animate-out", "zoom-out", "duration-200"}},
    {"scale-in", {"animate-in", "scale-in", "duration-200"}},
    {"scale-out", {"animate-out", "scale-out", "duration-200"}},
};

// Theme integration tokens
static const std::map<std::string, std::string> theme_tokens = {
    {"color-primary", "hsl(var(--primary))"},
    {"color-secondary", "hsl(var(--secondary))"},
    {"color-accent", "hsl(var(--accent))"},
    {"color-destructive", "hsl(var(--destructive))"},
    {"color-muted", "hsl(var(--muted))"},
    {"color-border", "hsl(var(--border))"},
    {"color-background", "hsl(var(--background))"},
    {"color-foreground", "hsl(var(--foreground))"},
    {"radius-sm", "calc(var(--radius) - 4px)"},
    {"radius-md", "var(--radius)"},
    {"radius-lg", "calc(var(--radius) + 4px)"},
};

// Get Radix UI import for C++ component name
std::string get_radix_import(const std::string& cpp_component_name) {
    auto it = radix_components.find(cpp_component_name);
    if (it != radix_components.end()) {
        return it->second;
    }
    return "";
}

// Generate Radix UI component wrapper with composition support
std::string generate_radix_component(
    const std::string& component_name,
    const std::string& radix_package,
    const std::vector<std::string>& props,
    const std::vector<std::string>& subcomponents = {},
    const std::map<std::string, std::string>& accessibility = {},
    const std::string& animation = "",
    const std::map<std::string, std::string>& theme_overrides = {}
) {
    std::string result = "import * as " + component_name + "Radix from '" + radix_package + "';\n";
    result += "import { cn } from '@/lib/utils';\n\n";
    
    // Generate subcomponent exports for composition
    for (const auto& subcomp : subcomponents) {
        result += "export const " + component_name + subcomp + " = " + component_name + "Radix." + subcomp + ";\n";
    }
    result += "\n";
    
    result += "export const " + component_name + ": React.FC<" + component_name + "Props> = (props) => {\n";
    result += "  const className = cn(\n";
    
    // Add theme classes
    if (!theme_overrides.empty()) {
        for (const auto& [token, value] : theme_overrides) {
            result += "    \"" + token + "\",\n";
        }
    }
    
    // Add animation classes
    if (!animation.empty()) {
        auto anim_it = animation_presets.find(animation);
        if (anim_it != animation_presets.end()) {
            for (const auto& anim_class : anim_it->second) {
                result += "    \"" + anim_class + "\",\n";
            }
        }
    }
    
    result += "    props.className\n";
    result += "  );\n\n";
    
    result += "  return (\n";
    result += "    <" + component_name + "Radix.Root";
    
    // Add props
    for (const auto& prop : props) {
        result += " " + prop + "={props." + prop + "}";
    }
    
    // Add accessibility attributes
    for (const auto& [aria_attr, react_attr] : accessibility) {
        auto acc_it = accessibility_attrs.find(aria_attr);
        if (acc_it != accessibility_attrs.end()) {
            result += " " + acc_it->second + "={props." + react_attr + "}";
        }
    }
    
    result += " className={className}";
    result += ">\n";
    result += "      {props.children}\n";
    result += "    </" + component_name + "Radix.Root>\n";
    result += "  );\n";
    result += "};\n";
    
    return result;
}

// Generate composition pattern (compound components)
std::string generate_composition_pattern(
    const std::string& component_name,
    const std::vector<std::string>& subcomponents
) {
    std::string result = "// Composition pattern for " + component_name + "\n";
    result += "export const " + component_name + "Composition = {\n";
    result += "  Root: " + component_name + "Radix.Root,\n";
    
    for (const auto& subcomp : subcomponents) {
        result += "  " + subcomp + ": " + component_name + "Radix." + subcomp + ",\n";
    }
    
    result += "} as const;\n";
    return result;
}

// Generate accessibility wrapper
std::string generate_accessibility_wrapper(
    const std::string& component_name,
    const std::map<std::string, std::string>& aria_attributes
) {
    std::string result = "export const " + component_name + "Accessible: React.FC<" + component_name + "Props> = (props) => {\n";
    result += "  const accessibilityProps = {\n";
    
    for (const auto& [aria_attr, react_attr] : aria_attributes) {
        auto acc_it = accessibility_attrs.find(aria_attr);
        if (acc_it != accessibility_attrs.end()) {
            result += "    " + acc_it->second + ": props." + react_attr + ",\n";
        }
    }
    
    result += "  };\n\n";
    result += "  return <" + component_name + " {...props} {...accessibilityProps} />;\n";
    result += "};\n";
    return result;
}

// Generate animation wrapper
std::string generate_animation_wrapper(
    const std::string& component_name,
    const std::string& animation_type
) {
    auto anim_it = animation_presets.find(animation_type);
    if (anim_it == animation_presets.end()) {
        return "";
    }
    
    std::string result = "export const " + component_name + "Animated: React.FC<" + component_name + "Props> = (props) => {\n";
    result += "  const animationClasses = cn(\n";
    
    for (const auto& anim_class : anim_it->second) {
        result += "    \"" + anim_class + "\",\n";
    }
    
    result += "    props.className\n";
    result += "  );\n\n";
    result += "  return <" + component_name + " {...props} className={animationClasses} />;\n";
    result += "};\n";
    return result;
}

// Generate theme integration
std::string generate_theme_integration(
    const std::string& component_name,
    const std::map<std::string, std::string>& theme_mapping
) {
    std::string result = "export const " + component_name + "Themed: React.FC<" + component_name + "Props> = (props) => {\n";
    result += "  const themeClasses = cn(\n";
    
    for (const auto& [token, value] : theme_mapping) {
        auto token_it = theme_tokens.find(token);
        if (token_it != theme_tokens.end()) {
            result += "    \"" + token + "\",\n";
        }
    }
    
    result += "    props.className\n";
    result += "  );\n\n";
    result += "  return <" + component_name + " {...props} className={themeClasses} />;\n";
    result += "};\n";
    return result;
}

// Detect if C++ struct should use Radix UI
bool should_use_radix(const std::string& component_name) {
    return radix_components.find(component_name) != radix_components.end();
}

// Get all available Radix components
std::vector<std::string> get_all_radix_components() {
    std::vector<std::string> components;
    for (const auto& [name, _] : radix_components) {
        components.push_back(name);
    }
    return components;
}

} // namespace radix_binder
