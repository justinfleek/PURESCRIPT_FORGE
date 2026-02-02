// Tailwind CSS Class Generator: C++23 → Tailwind Classes
// Phase 6: Advanced Tailwind Features
#include <string>
#include <vector>
#include <map>
#include <set>
#include <sstream>
#include <regex>

namespace tailwind_generator {

// C++ style attribute to Tailwind class mapping
static const std::map<std::string, std::vector<std::string>> style_mappings = {
    // Layout
    {"flex", {"flex"}},
    {"grid", {"grid"}},
    {"inline-flex", {"inline-flex"}},
    {"inline-grid", {"inline-grid"}},
    
    // Flexbox
    {"flex-row", {"flex-row"}},
    {"flex-col", {"flex-col"}},
    {"flex-wrap", {"flex-wrap"}},
    {"flex-nowrap", {"flex-nowrap"}},
    {"items-start", {"items-start"}},
    {"items-center", {"items-center"}},
    {"items-end", {"items-end"}},
    {"justify-start", {"justify-start"}},
    {"justify-center", {"justify-center"}},
    {"justify-end", {"justify-between"}},
    {"justify-between", {"justify-between"}},
    {"justify-around", {"justify-around"}},
    {"justify-evenly", {"justify-evenly"}},
    
    // Spacing
    {"padding-small", {"p-2"}},
    {"padding-medium", {"p-4"}},
    {"padding-large", {"p-6"}},
    {"padding-x-small", {"px-2"}},
    {"padding-x-medium", {"px-4"}},
    {"padding-x-large", {"px-6"}},
    {"padding-y-small", {"py-2"}},
    {"padding-y-medium", {"py-4"}},
    {"padding-y-large", {"py-6"}},
    {"margin-small", {"m-2"}},
    {"margin-medium", {"m-4"}},
    {"margin-large", {"m-6"}},
    
    // Colors
    {"bg-primary", {"bg-blue-500"}},
    {"bg-secondary", {"bg-gray-500"}},
    {"bg-success", {"bg-green-500"}},
    {"bg-danger", {"bg-red-500"}},
    {"bg-warning", {"bg-yellow-500"}},
    {"text-primary", {"text-blue-500"}},
    {"text-secondary", {"text-gray-500"}},
    
    // Typography
    {"text-sm", {"text-sm"}},
    {"text-base", {"text-base"}},
    {"text-lg", {"text-lg"}},
    {"text-xl", {"text-xl"}},
    {"text-2xl", {"text-2xl"}},
    {"font-bold", {"font-bold"}},
    {"font-semibold", {"font-semibold"}},
    {"font-normal", {"font-normal"}},
    
    // Borders
    {"border", {"border"}},
    {"border-2", {"border-2"}},
    {"rounded", {"rounded"}},
    {"rounded-md", {"rounded-md"}},
    {"rounded-lg", {"rounded-lg"}},
    {"rounded-full", {"rounded-full"}},
    
    // Shadows
    {"shadow", {"shadow"}},
    {"shadow-md", {"shadow-md"}},
    {"shadow-lg", {"shadow-lg"}},
    
    // Transitions
    {"transition", {"transition"}},
    {"transition-all", {"transition-all"}},
    {"duration-200", {"duration-200"}},
    {"duration-300", {"duration-300"}},
    
    // Hover states
    {"hover:bg-blue-600", {"hover:bg-blue-600"}},
    {"hover:bg-gray-600", {"hover:bg-gray-600"}},
    {"hover:scale-105", {"hover:scale-105"}},
    
    // Focus states
    {"focus:outline-none", {"focus:outline-none"}},
    {"focus:ring-2", {"focus:ring-2"}},
    {"focus:ring-blue-500", {"focus:ring-blue-500"}},
    
    // Disabled states
    {"disabled:opacity-50", {"disabled:opacity-50"}},
    {"disabled:cursor-not-allowed", {"disabled:cursor-not-allowed"}},
};

// Responsive breakpoints
static const std::vector<std::string> breakpoints = {
    "sm", "md", "lg", "xl", "2xl"
};

// Dark mode variants
static const std::vector<std::string> dark_mode_variants = {
    "dark:bg-gray-900",
    "dark:text-white",
    "dark:border-gray-700",
    "dark:hover:bg-gray-800",
};

// Animation classes
static const std::map<std::string, std::vector<std::string>> animation_classes = {
    {"spin", {"animate-spin"}},
    {"ping", {"animate-ping"}},
    {"pulse", {"animate-pulse"}},
    {"bounce", {"animate-bounce"}},
    {"fade-in", {"animate-in", "fade-in", "duration-200"}},
    {"slide-in", {"animate-in", "slide-in-from-top", "duration-300"}},
    {"zoom-in", {"animate-in", "zoom-in", "duration-200"}},
};

// Custom theme tokens
static const std::map<std::string, std::string> theme_tokens = {
    {"primary", "hsl(var(--primary))"},
    {"secondary", "hsl(var(--secondary))"},
    {"accent", "hsl(var(--accent))"},
    {"destructive", "hsl(var(--destructive))"},
    {"muted", "hsl(var(--muted))"},
    {"border", "hsl(var(--border))"},
    {"background", "hsl(var(--background))"},
    {"foreground", "hsl(var(--foreground))"},
};

// Convert C++ style attributes to Tailwind classes
std::string generate_tailwind_classes(const std::vector<std::string>& styles) {
    std::vector<std::string> classes;
    
    for (const auto& style : styles) {
        auto it = style_mappings.find(style);
        if (it != style_mappings.end()) {
            classes.insert(classes.end(), it->second.begin(), it->second.end());
        } else {
            // Pass through unknown styles (might be direct Tailwind classes)
            classes.push_back(style);
        }
    }
    
    // Remove duplicates
    std::sort(classes.begin(), classes.end());
    classes.erase(std::unique(classes.begin(), classes.end()), classes.end());
    
    // Join with spaces
    std::ostringstream oss;
    for (size_t i = 0; i < classes.size(); ++i) {
        if (i > 0) oss << " ";
        oss << classes[i];
    }
    
    return oss.str();
}

// Generate responsive classes with breakpoints
std::string generate_responsive_classes(
    const std::map<std::string, std::vector<std::string>>& breakpoint_styles
) {
    std::vector<std::string> classes;
    
    // Default (mobile-first)
    auto default_it = breakpoint_styles.find("default");
    if (default_it != breakpoint_styles.end()) {
        for (const auto& style : default_it->second) {
            classes.push_back(style);
        }
    }
    
    // Responsive breakpoints
    for (const auto& breakpoint : breakpoints) {
        auto bp_it = breakpoint_styles.find(breakpoint);
        if (bp_it != breakpoint_styles.end()) {
            for (const auto& style : bp_it->second) {
                classes.push_back(breakpoint + ":" + style);
            }
        }
    }
    
    return generate_tailwind_classes(classes);
}

// Generate dark mode classes
std::string generate_dark_mode_classes(
    const std::vector<std::string>& light_styles,
    const std::vector<std::string>& dark_styles
) {
    std::vector<std::string> classes;
    
    // Light mode (default)
    classes.insert(classes.end(), light_styles.begin(), light_styles.end());
    
    // Dark mode variants
    for (const auto& dark_style : dark_styles) {
        classes.push_back("dark:" + dark_style);
    }
    
    return generate_tailwind_classes(classes);
}

// Generate custom theme classes
std::string generate_theme_classes(
    const std::map<std::string, std::string>& theme_mapping
) {
    std::vector<std::string> classes;
    
    for (const auto& [property, token] : theme_mapping) {
        auto token_it = theme_tokens.find(token);
        if (token_it != theme_tokens.end()) {
            // Generate CSS variable class
            std::string class_name = property + "-[var(--" + token + ")]";
            classes.push_back(class_name);
        }
    }
    
    return generate_tailwind_classes(classes);
}

// Generate animation classes
std::string generate_animation_classes(const std::string& animation_type) {
    auto anim_it = animation_classes.find(animation_type);
    if (anim_it != animation_classes.end()) {
        return generate_tailwind_classes(anim_it->second);
    }
    return "";
}

// Generate arbitrary value classes
std::string generate_arbitrary_value_class(
    const std::string& property,
    const std::string& value
) {
    // Format: property-[value]
    return property + "-[" + value + "]";
}

// Generate multiple arbitrary values
std::string generate_arbitrary_classes(
    const std::map<std::string, std::string>& arbitrary_values
) {
    std::vector<std::string> classes;
    
    for (const auto& [property, value] : arbitrary_values) {
        classes.push_back(generate_arbitrary_value_class(property, value));
    }
    
    return generate_tailwind_classes(classes);
}

// Generate Tailwind className prop with all features
std::string generate_class_name_prop(
    const std::vector<std::string>& styles,
    const std::map<std::string, std::vector<std::string>>& responsive = {},
    const std::vector<std::string>& dark_styles = {},
    const std::map<std::string, std::string>& theme = {},
    const std::string& animation = "",
    const std::map<std::string, std::string>& arbitrary = {},
    const std::string& additional_classes = ""
) {
    std::vector<std::string> all_classes;
    
    // Base styles
    std::string base = generate_tailwind_classes(styles);
    if (!base.empty()) {
        std::istringstream iss(base);
        std::string cls;
        while (iss >> cls) {
            all_classes.push_back(cls);
        }
    }
    
    // Responsive classes
    if (!responsive.empty()) {
        std::string responsive_str = generate_responsive_classes(responsive);
        if (!responsive_str.empty()) {
            std::istringstream iss(responsive_str);
            std::string cls;
            while (iss >> cls) {
                all_classes.push_back(cls);
            }
        }
    }
    
    // Dark mode classes
    if (!dark_styles.empty()) {
        std::string dark_str = generate_dark_mode_classes(styles, dark_styles);
        if (!dark_str.empty()) {
            std::istringstream iss(dark_str);
            std::string cls;
            while (iss >> cls) {
                all_classes.push_back(cls);
            }
        }
    }
    
    // Theme classes
    if (!theme.empty()) {
        std::string theme_str = generate_theme_classes(theme);
        if (!theme_str.empty()) {
            std::istringstream iss(theme_str);
            std::string cls;
            while (iss >> cls) {
                all_classes.push_back(cls);
            }
        }
    }
    
    // Animation classes
    if (!animation.empty()) {
        std::string anim_str = generate_animation_classes(animation);
        if (!anim_str.empty()) {
            std::istringstream iss(anim_str);
            std::string cls;
            while (iss >> cls) {
                all_classes.push_back(cls);
            }
        }
    }
    
    // Arbitrary value classes
    if (!arbitrary.empty()) {
        std::string arb_str = generate_arbitrary_classes(arbitrary);
        if (!arb_str.empty()) {
            std::istringstream iss(arb_str);
            std::string cls;
            while (iss >> cls) {
                all_classes.push_back(cls);
            }
        }
    }
    
    // Additional classes
    if (!additional_classes.empty()) {
        std::istringstream iss(additional_classes);
        std::string cls;
        while (iss >> cls) {
            all_classes.push_back(cls);
        }
    }
    
    // Remove duplicates
    std::set<std::string> unique_classes(all_classes.begin(), all_classes.end());
    
    // Join with spaces
    std::ostringstream oss;
    bool first = true;
    for (const auto& cls : unique_classes) {
        if (!first) oss << " ";
        oss << cls;
        first = false;
    }
    
    std::string final_classes = oss.str();
    
    if (final_classes.empty()) {
        return "";
    }
    
    return "className={cn(\"" + final_classes + "\")}";
}

} // namespace tailwind_generator
