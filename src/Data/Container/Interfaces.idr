module Data.Container.Interfaces

import Data.Container.Object.Instances
import Data.Container.Object.Definition
import Data.Container.Products
import Data.Container.Extension.Definition
import public Data.Container.Morphism.Definition

import public Data.List.Quantifiers

public export
interface TensorMonoid (0 c : Cont) where
  tensorN : Scalar =%> c
  tensorM : (c >< c) =%> c

public export
interface SeqMonoid (0 c : Cont) where
  seqN : Scalar =%> c
  seqM : (c >@ c) =%> c

public export
interface CoprodMonoid (0 c : Cont) where
  plusN : Empty =%> c
  plusM : (c >+< c) =%> c

public export
interface ProdMonoid (0 c : Cont) where
  prodN : UnitCont =%> c
  prodM : (c >*< c) =%> c

public export
AllApplicative : List Cont -> Type
AllApplicative = All TensorMonoid

public export
(tt : TensorMonoid c) => Applicative (Ext c) where
  pure x = (tensorN @{tt}).fwd () <| (const x)
  (f <| f') <*> (x <| x') =
    let (q1 ** qq) = (%! tensorM @{tt}) (f, x)
    in q1 <| (\z => let (p1, p2) = qq z in f' p1 (x' p2))

public export
[FromSeq] (tt : SeqMonoid c) => Applicative (Ext c) where
  pure x = seqN.fwd () <| (const x)
  (f <| f') <*> (x <| x') = ?notAThing

public export
(tt : SeqMonoid c) => Monad (Ext c) using FromSeq where
  join (a <| b) = let (q1 ** q2) = (%! seqM @{tt}) (a <| shapeExt . b)
                   in q1 <| ((\xx => (b xx.fst).index xx.snd) . q2)

public export
[FromProd] (tt : ProdMonoid c) => Applicative (Ext c) where
  pure x = prodN.fwd () <| const x
  (<*>) = ?notAThing2


public export
(tt : ProdMonoid c) => Alternative (Ext c) using FromProd where
  empty = let (p1 ** p2) = (%! prodN @{tt}) () in p1 <| absurd . p2
  (<|>) (a <| a') (b <| b') =
    let (m1 ** m2) = (%! prodM @{tt}) (a, b) in m1 <| either a' b' . m2

