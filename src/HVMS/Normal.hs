module HVMS.Normal where

import HVMS.Type
import HVMS.Inject
import HVMS.Extract

-- | Normalizes a Net to normal form
normalize :: Net -> IO Net
normalize net = do
  -- Initialize runtime
  hvmInit
  
  -- Convert to runtime terms
  root <- doInjectNet net
  
  -- Normalize using C runtime
  norm <- normal root
  
  -- Convert back to core terms
  result <- doExtractNet norm []
  
  -- Cleanup runtime
  hvmFree
  
  return result

-- | Normalizes a term, returning Nothing if it fails
normalizeIO :: Net -> IO (Maybe Net)
normalizeIO net = do
  result <- normalize net
  return (Just result)
