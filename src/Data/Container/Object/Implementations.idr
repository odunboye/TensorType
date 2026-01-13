module Data.Container.Object.Implementations

import Data.Container.Interfaces
import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Fin

export
TensorMonoid List where
  tensorN = !% \x => (0 ** absurd)
  tensorM = !% \x => ?bbb

export
TensorMonoid (Vect n) where
  tensorN = !% \x => (() ** const ())
  tensorM = !% \x => ?bbb2
