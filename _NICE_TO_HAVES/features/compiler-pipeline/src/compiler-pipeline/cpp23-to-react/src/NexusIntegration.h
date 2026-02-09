// Nexus Integration: Agent Launch Button Generator
// Integrates compiler-pipeline with Nexus agent system and engram attestation
#ifndef NEXUS_INTEGRATION_H
#define NEXUS_INTEGRATION_H

#include <string>
#include <vector>
#include <map>

// Forward declarations
struct CppStruct;
struct CppField;

namespace nexus_integration {

// Agent launch task configuration
struct AgentLaunchTask {
    std::string task_id;
    std::string task_description;
    std::string agent_type;  // "web_search", "content_extraction", "network_formation", "research"
    std::map<std::string, std::string> config;  // Agent-specific config
    bool requires_attestation = true;
};

// Generate React component with agent launch button
std::string generate_agent_launch_button(
    const AgentLaunchTask& task,
    const std::string& component_name = "AgentLaunchButton"
);

// Generate WebSocket client hook for Bridge Server communication
std::string generate_websocket_client_hook();

// Generate attestation hook for task completion
std::string generate_attestation_hook();

// Generate complete agent launch component with status tracking
std::string generate_agent_launch_component(const CppStruct& component_def);

// Check if component has nexus_agent_launch attribute
bool has_nexus_agent_launch(const CppStruct& component_def);

// Extract agent launch task from component
AgentLaunchTask extract_agent_task(const CppStruct& component_def);

} // namespace nexus_integration

#endif // NEXUS_INTEGRATION_H
