// Omega V1 Models Route FFI
// ONLY framework boundary operations - all business logic is pure PureScript

import { Database } from "@opencode-ai/console-core/drizzle/index.js";
import { KeyTable, WorkspaceTable, ModelTable } from "@opencode-ai/console-core/schema/index.js";
import { OmegaData } from "@opencode-ai/console-core/model.js";
import { eq, and, isNull } from "@opencode-ai/console-core/drizzle/index.js";

// Framework boundary: Get Omega data from console-core
export const omegaDataList = () => {
  return OmegaData.list();
};

// Database boundary: Get disabled models (uses Database DSL)
export const getDisabledModels = async (apiKey) => {
  try {
    const rows = await Database.use(async (tx) => {
      return await tx
        .select({
          model: ModelTable.model,
        })
        .from(KeyTable)
        .innerJoin(WorkspaceTable, eq(WorkspaceTable.id, KeyTable.workspaceID))
        .leftJoin(
          ModelTable,
          and(
            eq(ModelTable.workspaceID, KeyTable.workspaceID),
            isNull(ModelTable.timeDeleted)
          )
        )
        .where(
          and(
            eq(KeyTable.key, apiKey),
            isNull(KeyTable.timeDeleted)
          )
        );
    });
    return rows.map((row) => row.model).filter((m) => m !== null && m !== undefined);
  } catch (error) {
    return [];
  }
};

// System boundary: Get current timestamp
export const getCurrentTimestamp = () => {
  return Math.floor(Date.now() / 1000);
};

// Pure extraction: Get model IDs from record
export const getModelIdsFromRecord = (models) => {
  return Object.keys(models || {});
};

// Framework boundary: JSON encoding for HTTP response
export const toJsonString = (response) => {
  return JSON.stringify(response);
};

// Framework boundary: Create JSON HTTP response
export const jsonResponse = async (jsonString) => {
  return new Response(jsonString, {
    headers: {
      "Content-Type": "application/json",
    },
  });
};

// Framework boundary: Create text HTTP response
export const textResponse = async (text, status) => {
  return new Response(text, { status });
};

// Framework boundary: Get header from SolidJS Start APIEvent
export const getRequestHeader = (event, name) => {
  const value = event.request.headers.get(name);
  return value === null ? null : value;
};
