import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import D2RelationGap.Words

/-! Actual objects and targets, deliberately NOT asserted as proved theorems.
The six-relator quotient is OpenAI's original G. Removing t1 requires a proof.
No minimum over an empty set and no natural-number subtraction is used. -/
namespace D2RelationGap
namespace Targets

abbrev F := FreeGroup Gen

def freeLetter (l : Letter) : F :=
  if l.positive then FreeGroup.of l.gen else (FreeGroup.of l.gen)⁻¹

def freeWord (w : Word) : F := (w.map freeLetter).prod

def sourceRelations : Set F := {freeWord r1, freeWord r2, freeWord r3, freeWord r4}
def quotientRelations : Set F := sourceRelations ∪ {freeWord t1, freeWord t2}
def fiveRelations : Set F := sourceRelations ∪ {freeWord t2}

abbrev P := PresentedGroup sourceRelations
abbrev G := PresentedGroup quotientRelations
abbrev quotientMap : F →* G := PresentedGroup.mk quotientRelations
abbrev N : Subgroup F := quotientMap.ker
abbrev RelationCarrier := Additive (Abelianization N)
abbrev R := MonoidAlgebra ℤ G

def HasNormalGenerators (k : ℕ) : Prop :=
  ∃ v : Fin k → F, Subgroup.normalClosure (Set.range v) = N

def HasModuleGenerators {S V : Type*} [Semiring S] [AddCommMonoid V] [Module S V]
    (k : ℕ) : Prop :=
  ∃ v : Fin k → V, Submodule.span S (Set.range v) = ⊤

def NormalRankFive : Prop :=
  HasNormalGenerators 5 ∧ ∀ k, HasNormalGenerators k → 5 ≤ k

/-- This condition forbids a substitute action on an unrelated or incorrectly acted-on carrier.
The conjugate is passed as n' with an equality, avoiding an unproved membership constructor. -/
def CanonicalAction [Module R RelationCarrier] : Prop :=
  ∀ (f : F) (n n' : N), (n' : F) = f * (n : F) * f⁻¹ →
    (MonoidAlgebra.single (quotientMap f) (1 : ℤ) : R) •
      Additive.ofMul (Abelianization.of n) = Additive.ofMul (Abelianization.of n')

def IntegralRelationGapTarget [Module R RelationCarrier] : Prop :=
  CanonicalAction ∧
  HasModuleGenerators (S := R) (V := RelationCarrier) 4 ∧
  (∀ k, HasModuleGenerators (S := R) (V := RelationCarrier) k → 4 ≤ k) ∧
  NormalRankFive

/-- Global deficiency requires ALL finite epimorphisms, not just the fixed five generators.
Together with HasNormalGenerators 5 this is a minimum/maximum-free statement of deficiency 0. -/
def DeficiencyZeroTarget : Prop :=
  HasNormalGenerators 5 ∧
  ∀ (m k : ℕ) (q : FreeGroup (Fin m) →* G), Function.Surjective q →
    (∃ v : Fin k → FreeGroup (Fin m), Subgroup.normalClosure (Set.range v) = q.ker) → m ≤ k

end Targets
end D2RelationGap
