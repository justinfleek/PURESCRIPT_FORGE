-- | Web Content - Astro content configuration
-- | Phase 5: Desktop/Web Migration
module Opencode.Web.Content where

import Prelude

-- | Content collections configuration
-- | This matches Astro's content config structure
type ContentConfig =
  { collections :: Collections
  }

-- | Collections type
type Collections =
  { docs :: Collection
  }

-- | Collection definition
type Collection =
  { loader :: CollectionLoader
  , schema :: CollectionSchema
  }

-- | Collection loader (from Astro Starlight)
type CollectionLoader = Unit

-- | Collection schema (from Astro Starlight)
type CollectionSchema = Unit

-- | Define content collections
-- | This matches Astro's defineCollection function
collections :: ContentConfig
collections =
  { collections:
      { docs:
          { loader: docsLoader
          , schema: docsSchema
          }
      }
  }

-- | Docs loader
-- | In full Astro integration, this uses Astro's docsLoader()
-- | Returns unit as placeholder - actual implementation requires Astro integration
docsLoader :: CollectionLoader
docsLoader = unit

-- | Docs schema
-- | In full Astro integration, this uses Astro's docsSchema
-- | Returns unit as placeholder - actual implementation requires Astro integration
docsSchema :: CollectionSchema
docsSchema = unit
