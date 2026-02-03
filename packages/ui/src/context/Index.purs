-- | UI Context Module Index
-- |
-- | Re-exports all context modules for convenient importing.
module Forge.UI.Context
  ( module Forge.UI.Context.Helper
  , module Forge.UI.Context.Code
  , module Forge.UI.Context.Data
  , module Forge.UI.Context.Dialog
  , module Forge.UI.Context.Diff
  , module Forge.UI.Context.I18n
  , module Forge.UI.Context.Marked
  , module Forge.UI.Context.WorkerPool
  ) where

import Forge.UI.Context.Helper (SimpleContext, SimpleContextConfig, createSimpleContext, useContext, ContextProvider)
import Forge.UI.Context.Code (CodeComponentProvider, useCodeComponent, CodeComponentContext)
import Forge.UI.Context.Data (DataContext, DataProvider, useData, PermissionRespondFn, QuestionReplyFn, QuestionRejectFn, NavigateToSessionFn, DataStore)
import Forge.UI.Context.Dialog (DialogContext, DialogProvider, useDialog, DialogElement, ActiveDialog)
import Forge.UI.Context.Diff (DiffComponentProvider, useDiffComponent, DiffComponentContext)
import Forge.UI.Context.I18n (I18nContext, I18nProvider, useI18n, UiI18nKey, UiI18nParams, resolveTemplate)
import Forge.UI.Context.Marked (MarkedContext, MarkedProvider, useMarked, NativeMarkdownParser, parseMarkdown)
import Forge.UI.Context.WorkerPool (WorkerPools, WorkerPoolProvider, useWorkerPool, WorkerPoolManager, DiffStyle(..))
