import D2RelationGap.FoxSpan
import D2RelationGap.SourceIdentities
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.RingHom

/-! The canonical integral ZG-module on the actual relation abelianization.
Groups and character: OpenAI, A Counterexample to Wall's D(2) Problem (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
This constructs the action; it does not assume K perfectness or the relation gap. -/
namespace D2RelationGap.RelationModule
open Targets FoxSemantics Cyclotomic
noncomputable section

def conjugate (f : F) : N →* N where
  toFun n := ⟨f * (n : F) * f⁻¹, Subgroup.Normal.conj_mem (inferInstance : N.Normal) _ n.property f⟩
  map_one' := Subtype.ext (by simp)
  map_mul' n m := Subtype.ext (by simp [mul_assoc])

def freeEnd (f : F) : AddMonoid.End RelationCarrier :=
  (Abelianization.map (conjugate f)).toAdditive

theorem freeEnd_of (f : F) (n : N) :
    freeEnd f (Additive.ofMul (Abelianization.of n)) =
      Additive.ofMul (Abelianization.of (conjugate f n)) := rfl

def freeAction : F →* AddMonoid.End RelationCarrier where
  toFun := freeEnd
  map_one' := by
    apply AddMonoidHom.ext
    change ∀ v : Abelianization N, freeEnd 1 (Additive.ofMul v) = Additive.ofMul v
    intro v
    refine QuotientGroup.induction_on v (fun n => ?_)
    change Additive.ofMul (Abelianization.of (conjugate 1 n)) = Additive.ofMul (Abelianization.of n)
    have h : conjugate 1 n = n := Subtype.ext (by simp [conjugate])
    rw [h]
  map_mul' f g := by
    apply AddMonoidHom.ext
    change ∀ v : Abelianization N, freeEnd (f * g) (Additive.ofMul v) =
      freeEnd f (freeEnd g (Additive.ofMul v))
    intro v
    refine QuotientGroup.induction_on v (fun n => ?_)
    change Additive.ofMul (Abelianization.of (conjugate (f * g) n)) =
      Additive.ofMul (Abelianization.of (conjugate f (conjugate g n)))
    have h : conjugate (f * g) n = conjugate f (conjugate g n) :=
      Subtype.ext (by simp [conjugate, mul_assoc])
    rw [h]

/-- Elements of N act by inner conjugation, hence trivially on its abelianization. -/
theorem freeAction_kernel (f : F) (hf : f ∈ N) : freeAction f = 1 := by
  apply AddMonoidHom.ext
  change ∀ v : Abelianization N, freeEnd f (Additive.ofMul v) = Additive.ofMul v
  intro v
  refine QuotientGroup.induction_on v (fun n => ?_)
  change Additive.ofMul (Abelianization.of (conjugate f n)) = Additive.ofMul (Abelianization.of n)
  have h : conjugate f n = (⟨f, hf⟩ : N) * n * (⟨f, hf⟩ : N)⁻¹ := Subtype.ext rfl
  rw [h]
  simp [mul_comm]

def quotientAction : G →* AddMonoid.End RelationCarrier :=
  QuotientGroup.lift (Subgroup.normalClosure quotientRelations) freeAction (by
    rw [← original_kernel_eq]
    exact freeAction_kernel)

theorem quotientAction_quotient (f : F) : quotientAction (quotientMap f) = freeAction f := rfl

def ringAction : R →+* AddMonoid.End RelationCarrier :=
  MonoidAlgebra.liftNCRingHom (Int.castRingHom _) quotientAction (fun z _g => Int.cast_commute z _)

instance relationModule : Module R RelationCarrier := Module.compHom RelationCarrier ringAction

theorem single_smul (g : G) (z : ℤ) (v : RelationCarrier) :
    (MonoidAlgebra.single g z : R) • v = z • quotientAction g v := by
  change ringAction (MonoidAlgebra.single g z) v = _
  rw [ringAction, MonoidAlgebra.liftNCRingHom_single]
  rfl

theorem canonicalAction : Targets.CanonicalAction := by
  intro f n n' h
  rw [single_smul, one_smul, quotientAction_quotient]
  change Additive.ofMul (Abelianization.of (conjugate f n)) = Additive.ofMul (Abelianization.of n')
  have heq : conjugate f n = n' := Subtype.ext h.symm
  rw [heq]

def scalarCharacter : R →+* E :=
  MonoidAlgebra.liftNCRingHom (Int.castRingHom _) Character.rho
    (fun z _g => Int.cast_commute z _)

instance evaluatedModule : Module R Vector := Module.compHom Vector scalarCharacter

theorem scalarCharacter_single (g : G) (z : ℤ) :
    scalarCharacter (MonoidAlgebra.single g z) = (z : E) * Character.rho g := by
  rw [scalarCharacter, MonoidAlgebra.liftNCRingHom_single]
  rfl

theorem fox_quotientAction (g : G) (v : RelationCarrier) :
    abelianizedDerivative (quotientAction g v) = Character.rho g • abelianizedDerivative v := by
  obtain ⟨f, rfl⟩ := PresentedGroup.mk_surjective quotientRelations g
  rw [quotientAction_quotient]
  revert v
  change ∀ v : Abelianization N,
    abelianizedDerivative (freeEnd f (Additive.ofMul v)) =
      Character.rho (quotientMap f) • abelianizedDerivative (Additive.ofMul v)
  intro v
  refine QuotientGroup.induction_on v (fun n => ?_)
  change abelianizedDerivative (freeEnd f (Additive.ofMul (Abelianization.of n))) =
    Character.rho (quotientMap f) • abelianizedDerivative (Additive.ofMul (Abelianization.of n))
  rw [freeEnd_of]
  exact abelianizedDerivative_conjugate f n (conjugate f n) rfl

theorem fox_single_smul (g : G) (z : ℤ) (v : RelationCarrier) :
    abelianizedDerivative ((MonoidAlgebra.single g z : R) • v) =
      scalarCharacter (MonoidAlgebra.single g z) • abelianizedDerivative v := by
  rw [single_smul, map_zsmul, fox_quotientAction, scalarCharacter_single]
  funext h
  change z • (Character.rho g * abelianizedDerivative v h) =
    ((z : E) * Character.rho g) * abelianizedDerivative v h
  simp [zsmul_eq_mul, mul_assoc]

theorem fox_smul (r : R) (v : RelationCarrier) :
    abelianizedDerivative (r • v) = scalarCharacter r • abelianizedDerivative v := by
  rw [← r.sum_coeff_single]
  simp only [Finsupp.sum, Finset.sum_smul, map_sum]
  exact Finset.sum_congr rfl (fun g _ => fox_single_smul g (r.coeff g) v)

/-- Genuine ZG-linearity for the canonical integral action and character specialization. -/
def foxLinear : RelationCarrier →ₗ[R] Vector where
  toAddHom := abelianizedDerivative
  map_smul' := fox_smul

def scalarComplexCharacter : R →+* ℂ := ComplexCharacter.complexEmbedding.comp scalarCharacter

instance evaluatedComplexModule : Module R (Gen → ℂ) :=
  Module.compHom (Gen → ℂ) scalarComplexCharacter

theorem scalarComplexCharacter_single (g : G) (z : ℤ) :
    scalarComplexCharacter (MonoidAlgebra.single g z) = (z : ℂ) * ComplexCharacter.rho g := by
  rw [scalarComplexCharacter, RingHom.comp_apply, scalarCharacter_single, map_mul, map_intCast]
  rfl

def complexFoxLinear : RelationCarrier →ₗ[R] (Gen → ℂ) where
  toFun v := fun g => ComplexCharacter.complexEmbedding (abelianizedDerivative v g)
  map_add' v w := by
    funext g
    change ComplexCharacter.complexEmbedding (abelianizedDerivative (v + w) g) = _
    rw [map_add]
    exact map_add _ _ _
  map_smul' r v := by
    funext g
    change ComplexCharacter.complexEmbedding (abelianizedDerivative (r • v) g) =
      ComplexCharacter.complexEmbedding (scalarCharacter r) *
        ComplexCharacter.complexEmbedding (abelianizedDerivative v g)
    rw [fox_smul]
    exact map_mul _ _ _

theorem complexFoxLinear_of (n : N) :
    complexFoxLinear (Additive.ofMul (Abelianization.of n)) = complexDerivative (n : F) := rfl

def sourceClass (i : Fin 4) : RelationCarrier :=
  Additive.ofMul (Abelianization.of (⟨_, FoxSpan.sourceRelator_mem_kernel i⟩ : N))

theorem foxLinear_sourceClass (i : Fin 4) : foxLinear (sourceClass i) = FoxRank.sourceRows i := rfl

theorem complexFoxLinear_sourceClass (i : Fin 4) :
    complexFoxLinear (sourceClass i) = FoxRank.complexSourceRows i := rfl

theorem module_generators_image_span {k : ℕ} (v : Fin k → RelationCarrier)
    (hv : Submodule.span R (Set.range v) = ⊤) (m : RelationCarrier) :
    foxLinear m ∈ Submodule.span E (Set.range (fun j => foxLinear (v j))) := by
  have hm : m ∈ Submodule.span R (Set.range v) := by rw [hv]; trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨j, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    change abelianizedDerivative (r • x) ∈ _
    rw [fox_smul]
    exact Submodule.smul_mem _ _ hx

/-- Every finite generating family of the actual integral relation module has size at least four. -/
theorem module_generators_at_least_four {k : ℕ}
    (h : HasModuleGenerators (S := R) (V := RelationCarrier) k) : 4 ≤ k := by
  obtain ⟨v, hv⟩ := h
  have hspan : Submodule.span E (Set.range FoxRank.sourceRows) ≤
      Submodule.span E (Set.range (fun j => foxLinear (v j))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← foxLinear_sourceClass]
    exact module_generators_image_span v hv (sourceClass i)
  have hdim := Submodule.finrank_mono hspan
  rw [FoxRank.sourceRows_span_dimension] at hdim
  exact hdim.trans (by simpa only [Set.finrank, Fintype.card_fin] using
    finrank_range_le_card (R := E) (fun j => foxLinear (v j)))

def classOf (n : N) : RelationCarrier := Additive.ofMul (Abelianization.of n)

theorem classOf_mul (n m : N) : classOf (n * m) = classOf n + classOf m := by
  change Abelianization.of (n * m) = Abelianization.of n * Abelianization.of m
  exact map_mul _ _ _

theorem classOf_inv (n : N) : classOf n⁻¹ = -classOf n := by
  change Abelianization.of n⁻¹ = (Abelianization.of n)⁻¹
  exact map_inv _ _

def classKernel (V : Submodule R RelationCarrier) : Subgroup F where
  carrier := {f | ∃ hf : f ∈ N, classOf (⟨f, hf⟩ : N) ∈ V}
  one_mem' := ⟨N.one_mem, by change Additive.ofMul (Abelianization.of (1 : N)) ∈ V; simp⟩
  mul_mem' := by
    rintro f g ⟨hf, hcf⟩ ⟨hg, hcg⟩
    refine ⟨N.mul_mem hf hg, ?_⟩
    change classOf ((⟨f, hf⟩ : N) * (⟨g, hg⟩ : N)) ∈ V
    rw [classOf_mul]
    exact V.add_mem hcf hcg
  inv_mem' := by
    rintro f ⟨hf, hcf⟩
    refine ⟨N.inv_mem hf, ?_⟩
    change classOf (⟨f, hf⟩ : N)⁻¹ ∈ V
    rw [classOf_inv]
    exact V.neg_mem hcf

instance classKernel_normal (V : Submodule R RelationCarrier) : (classKernel V).Normal where
  conj_mem := by
    rintro n ⟨hn, hcn⟩ f
    have hmem := Subgroup.Normal.conj_mem (inferInstance : N.Normal) n hn f
    refine ⟨hmem, ?_⟩
    have hc := canonicalAction f (⟨n, hn⟩ : N) (⟨f * n * f⁻¹, hmem⟩ : N) rfl
    change Additive.ofMul (Abelianization.of (⟨f * n * f⁻¹, hmem⟩ : N)) ∈ V
    rw [← hc]
    exact V.smul_mem _ hcn

/-- Normal generators give module generators on the actual canonically acted-on abelianization. -/
theorem normal_generators_give_module_generators {k : ℕ} (h : HasNormalGenerators k) :
    HasModuleGenerators (S := R) (V := RelationCarrier) k := by
  obtain ⟨v, hv⟩ := h
  have hn (j : Fin k) : v j ∈ N := by
    rw [← hv]
    exact Subgroup.subset_normalClosure ⟨j, rfl⟩
  let w : Fin k → RelationCarrier := fun j => classOf (⟨v j, hn j⟩ : N)
  let V := Submodule.span R (Set.range w)
  have hN : N ≤ classKernel V := by
    rw [← hv]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    exact ⟨hn j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨w, Submodule.eq_top_iff'.mpr ?_⟩
  change ∀ m : Abelianization N, Additive.ofMul m ∈ V
  intro m
  refine QuotientGroup.induction_on m (fun n => ?_)
  obtain ⟨_, hcn⟩ := hN n.property
  exact hcn

theorem hasModuleGenerators_five : HasModuleGenerators (S := R) (V := RelationCarrier) 5 :=
  normal_generators_give_module_generators hasNormalGenerators_five

/-- Replacing the canonical x1 action by the trivial action fails on an actual relator class. -/
theorem corrupted_trivial_action_rejected :
    (MonoidAlgebra.single (quotientMap (FreeGroup.of .x1)) (1 : ℤ) : R) • sourceClass 0 ≠
      sourceClass 0 := by
  have hv : abelianizedDerivative (sourceClass 0) .a1 = (-2 : E) := by
    change derivative (freeWord r1) .a1 = -2
    rw [foxRow_sound]
    have he : CycloPair.foxRow r1 .a1 = (⟨-2,0⟩ : CycloPair) := by decide
    rw [he]
    simp [evalPair]
  intro h
  have hd := congrArg (fun v => abelianizedDerivative v .a1) h
  rw [fox_smul, scalarCharacter_single, Character.rho_x1] at hd
  change (1 : E) * (-1 : E) * abelianizedDerivative (sourceClass 0) .a1 =
    abelianizedDerivative (sourceClass 0) .a1 at hd
  rw [hv] at hd
  norm_num at hd

end
end D2RelationGap.RelationModule
