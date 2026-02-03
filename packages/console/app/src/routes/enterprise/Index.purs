-- | Enterprise Index Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/enterprise/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Enterprise.Index
  ( EnterpriseFormData(..)
  , EnterpriseState(..)
  , EnterpriseAction(..)
  , FaqItem(..)
  , initialState
  , reducer
  , enterpriseFaqs
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Enterprise contact form data
type EnterpriseFormData =
  { name :: String
  , role :: String
  , email :: String
  , message :: String
  }

-- | Empty form data
emptyFormData :: EnterpriseFormData
emptyFormData =
  { name: ""
  , role: ""
  , email: ""
  , message: ""
  }

-- | Page state
type EnterpriseState =
  { formData :: EnterpriseFormData
  , isSubmitting :: Boolean
  , showSuccess :: Boolean
  }

-- | Initial state
initialState :: EnterpriseState
initialState =
  { formData: emptyFormData
  , isSubmitting: false
  , showSuccess: false
  }

-- | Page actions
data EnterpriseAction
  = UpdateName String
  | UpdateRole String
  | UpdateEmail String
  | UpdateMessage String
  | StartSubmit
  | SubmitSuccess
  | SubmitError
  | HideSuccess
  | ResetForm

derive instance eqEnterpriseAction :: Eq EnterpriseAction

-- | State reducer (pure)
reducer :: EnterpriseState -> EnterpriseAction -> EnterpriseState
reducer state action = case action of
  UpdateName name ->
    state { formData = state.formData { name = name } }
  UpdateRole role ->
    state { formData = state.formData { role = role } }
  UpdateEmail email ->
    state { formData = state.formData { email = email } }
  UpdateMessage message ->
    state { formData = state.formData { message = message } }
  StartSubmit ->
    state { isSubmitting = true }
  SubmitSuccess ->
    state { isSubmitting = false, showSuccess = true, formData = emptyFormData }
  SubmitError ->
    state { isSubmitting = false }
  HideSuccess ->
    state { showSuccess = false }
  ResetForm ->
    initialState

-- | FAQ item
type FaqItem =
  { question :: String
  , answer :: String
  }

-- | Enterprise FAQs
enterpriseFaqs :: Array FaqItem
enterpriseFaqs =
  [ { question: "What is OpenCode Enterprise?"
    , answer: "OpenCode Enterprise is for organizations that want to ensure that their code and data never leaves their infrastructure. It can do this by using a centralized config that integrates with your SSO and internal AI gateway."
    }
  , { question: "How do I get started with OpenCode Enterprise?"
    , answer: "Simply start with an internal trial with your team. OpenCode by default does not store your code or context data, making it easy to get started. Then contact us to discuss pricing and implementation options."
    }
  , { question: "How does enterprise pricing work?"
    , answer: "We offer per-seat enterprise pricing. If you have your own LLM gateway, we do not charge for tokens used. For further details, contact us for a custom quote based on your organization's needs."
    }
  , { question: "Is my data secure with OpenCode Enterprise?"
    , answer: "Yes. OpenCode does not store your code or context data. All processing happens locally or through direct API calls to your AI provider. With central config and SSO integration, your data remains secure within your organization's infrastructure."
    }
  ]
