// FFI for Sidepanel.Utils.Worktree
// Module-level mutable state for worktree tracking

import * as $Map from "../Data.Map.Internal/index.js";

// Use the actual PureScript Leaf constructor for empty Maps
var emptyMap = $Map.empty;

export const stateMap = { value: emptyMap };

export const waitersMap = { value: emptyMap };
