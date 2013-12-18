-- | Values are sequent-calculus terms where each intermediate result is named

module Value where

import Data.Set (Set)
import qualified Data.Set as Set

newtype Name = Name  { name :: String }   -- TODO: Integer
newtype Tag  = MkTag { tag  :: String }   -- TODO: Int

type Hyp  = Name -- ^ Hypothesis variable @x@.
type Conc = Name -- ^ Conclusion variable @y_@.

-- | Projections from Sigma-type.
data Proj
  = L  -- ^ Left / first projection.
  | R  -- ^ Right / second projection.

data PiSig
  = Pi     -- ^ Dependent function type.
  | Sigma  -- ^ Dependent pair type.

-- | Left-hand side terms aka. elimination/destruction/inferable terms.
data LTerm
  = LHyp Hyp         -- ^ Hypothesis   @x@  (indirection/alias).
  | App  Hyp Conc    -- ^ Application  @x y_@.
  | Proj Hyp Proj    -- ^ Projection   @x.p@.
  | Ann  RTerm Type  -- ^ Introduction @c : A@ (this is the cut!).

data RTerm
  = Conc Conc                -- ^ Conclusion var @y_@ (indirection/alias).
  | Hyp  Hyp                 -- ^ Hypothesis var @x@
  | Tag  Tag                 -- ^ Tag            @'t@.
  | Pair Conc Conc           -- ^ Pair           @(y1_, y2_)@.
  | Lam  Hyp  Term           -- ^ Lambda-abstr.  @\ x -> v@.
  | Quant PiSig Conc RTerm   -- ^ Quantifier Sigma @(x : Y_) & C@ or Pi @(x : Y_) -> C@.
  | Tags Tags                -- ^ Tagset           @{'t1,...,'tn}@.
  | Univ                     -- ^ Universe         @Type@.

type Type = Term
data Term
  = Let   Binds Term         -- ^ Let binding      @let bs in v@.
  | Case  Hyp Branches       -- ^ Case distinction @case x of brs@.
  | Core  RTerm              -- ^ Leaf.

type Branches = [(Tag,Term)] -- ^ @{ 't1 -> v1; ...; 'tn -> vn }@.

data Bind
  = LBind Hyp  LTerm  -- ^ @x = d@
  | RBind Conc RTerm  -- ^ @y_ = c@

type Binds = [Bind]
type Tags  = Set Tag
