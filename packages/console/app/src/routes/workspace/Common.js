// Workspace Common FFI
// Database and actor context operations

import { Actor } from "@opencode-ai/console-core/actor.js";
import { Database } from "@opencode-ai/console-core/drizzle/index.js";
import { UserTable, WorkspaceTable } from "@opencode-ai/console-core/schema/index.js";
import { eq, and, isNull, desc } from "@opencode-ai/console-core/drizzle/index.js";

// Get last seen workspace ID for current actor
export const getLastSeenWorkspaceID = async () => {
  try {
    const actor = Actor.assert("account");
    const result = await Database.use(async (tx) => {
      const rows = await tx
        .select({ id: WorkspaceTable.id })
        .from(UserTable)
        .innerJoin(WorkspaceTable, eq(UserTable.workspaceID, WorkspaceTable.id))
        .where(
          and(
            eq(UserTable.accountID, actor.properties.accountID),
            isNull(UserTable.timeDeleted),
            isNull(WorkspaceTable.timeDeleted)
          )
        )
        .orderBy(desc(UserTable.timeSeen))
        .limit(1);
      return rows[0]?.id;
    });
    return result === undefined ? null : result;
  } catch (error) {
    return null;
  }
};
