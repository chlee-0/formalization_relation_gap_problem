import D2RelationGap.GenericFox
import D2RelationGap.PresentationRose

/-!
Twisted H1 = 0 for EVERY finite epimorphism onto OpenAI's G, and the consequent bound
m <= k+1 for any presentation with m generators and k normal generators of the kernel.
The rank-five input is the checked source-row computation; `GenericFox.kernel_transfer`
moves it to an arbitrary free group. Excluding k = m-1 (and hence deficiency zero)
needs the presentation-complex obstruction for arbitrary rank and is NOT proved here.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies G, rho and the
source Fox rows.
-/
noncomputable section
namespace D2RelationGap.DeficiencyBound
open Targets GenericFox

/-- The original complex character on the fixed rank-five free group. -/
def χ5 : F →* ℂ := ComplexCharacter.rho.comp quotientMap

theorem D5_eq : D χ5 = FoxSemantics.complexDerivative :=
  (D_unique χ5 FoxSemantics.complexDerivative
    (fun u v => FoxSemantics.complexDerivative_mul u v)
    (fun g => PresentationRose.complexDerivative_of g)).symm

theorem boundaryOne5_eq : boundaryOne χ5 = ComplexFox.boundaryOne := by
  apply LinearMap.ext
  intro x
  rfl

/-- Rank five: the degree-one kernel is spanned by Fox vectors of the actual N. -/
theorem kernel5_le : LinearMap.ker (boundaryOne χ5) ≤ foxSpan χ5 N := by
  let S := Submodule.span ℂ (Set.range FoxRank.complexSourceRows)
  have hrow : ∀ i, FoxRank.complexSourceRows i = D χ5 (freeWord (FoxRank.sourceRelator i)) := by
    intro i; rw [D5_eq]; rfl
  have hSN : S ≤ foxSpan χ5 N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hrow]
    exact Submodule.subset_span ⟨_, FoxSpan.sourceRelator_mem_kernel i, rfl⟩
  have hSK : S ≤ LinearMap.ker (boundaryOne χ5) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hrow, fundamental]
    have hn := FoxSpan.sourceRelator_mem_kernel i
    have hq : quotientMap (freeWord (FoxRank.sourceRelator i)) = 1 := MonoidHom.mem_ker.mp hn
    simp [χ5, hq]
  have heq : S = LinearMap.ker (boundaryOne χ5) := by
    apply Submodule.eq_of_le_of_finrank_eq hSK
    rw [finrank_span_eq_card FoxRank.complexSourceRows_independent, boundaryOne5_eq,
      ComplexFox.boundaryOne_kernel_dimension]
    rfl
  rw [← heq]
  exact hSN

/-- Twisted H1 = 0 for an ARBITRARY finite epimorphism onto G: the degree-one kernel of
its free group is spanned by Fox vectors of its own kernel. -/
theorem kernel_le {m : ℕ} (q : FreeGroup (Fin m) →* G) (hq : Function.Surjective q) :
    LinearMap.ker (boundaryOne (ComplexCharacter.rho.comp q)) ≤
      foxSpan (ComplexCharacter.rho.comp q) q.ker := by
  choose a ha using fun g : Gen => hq (quotientMap (FreeGroup.of g))
  choose b hb using fun i : Fin m => PresentedGroup.mk_surjective quotientRelations (q (FreeGroup.of i))
  let α : F →* FreeGroup (Fin m) := FreeGroup.lift a
  let β : FreeGroup (Fin m) →* F := FreeGroup.lift b
  have hqα : q.comp α = quotientMap := FreeGroup.ext_hom _ _ (fun g => by simp [α, ha])
  have hqβ : quotientMap.comp β = q := FreeGroup.ext_hom _ _ (fun i => by simp [β, hb])
  have hqα' : ∀ f, q (α f) = quotientMap f := fun f => DFunLike.congr_fun hqα f
  have hqβ' : ∀ f, quotientMap (β f) = q f := fun f => DFunLike.congr_fun hqβ f
  apply kernel_transfer χ5 (ComplexCharacter.rho.comp q) N q.ker α β
  · ext f; simp [χ5, hqα']
  · ext f; simp [χ5, hqβ']
  · intro n hn
    rw [MonoidHom.mem_ker, hqα']
    exact hn
  · intro i
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqα', hqβ', inv_mul_cancel]
  · exact kernel5_le

/-- The character is nontrivial on some generator of any free presentation. -/
theorem exists_nontrivial {m : ℕ} (q : FreeGroup (Fin m) →* G) (hq : Function.Surjective q) :
    ∃ i, (ComplexCharacter.rho.comp q) (FreeGroup.of i) ≠ 1 := by
  by_contra h
  push Not at h
  have hc : ComplexCharacter.rho.comp q = 1 := FreeGroup.ext_hom _ _ (fun i => by simpa using h i)
  obtain ⟨x, hx⟩ := hq (quotientMap (FreeGroup.of .x1))
  have h1 := DFunLike.congr_fun hc x
  simp only [MonoidHom.coe_comp, Function.comp_apply, hx, MonoidHom.one_apply] at h1
  exact ComplexCharacter.rho_x1_nontrivial h1

/-- For EVERY epimorphism FreeGroup (Fin m) ->> G whose kernel is the normal closure of
k elements, m <= k + 1. (Deficiency zero additionally needs to exclude k = m - 1.) -/
theorem rank_le_succ (m k : ℕ) (q : FreeGroup (Fin m) →* G) (hq : Function.Surjective q)
    (v : Fin k → FreeGroup (Fin m)) (hv : Subgroup.normalClosure (Set.range v) = q.ker) :
    m ≤ k + 1 := by
  have hvk : ∀ j, (ComplexCharacter.rho.comp q) (v j) = 1 := by
    intro j
    have hm : v j ∈ q.ker := hv ▸ Subgroup.subset_normalClosure ⟨j, rfl⟩
    simp [MonoidHom.mem_ker.mp hm]
  have hspan : foxSpan (ComplexCharacter.rho.comp q) q.ker ≤
      Submodule.span ℂ (Set.range (fun j => D (ComplexCharacter.rho.comp q) (v j))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, hn, rfl⟩
    exact normalClosure_span _ v hvk n (hv ▸ hn)
  have hdim := Submodule.finrank_mono ((kernel_le q hq).trans hspan)
  have hk : Module.finrank ℂ (Submodule.span ℂ
      (Set.range (fun j => D (ComplexCharacter.rho.comp q) (v j)))) ≤ k := by
    have h := finrank_range_le_card (R := ℂ) (fun j => D (ComplexCharacter.rho.comp q) (v j))
    rw [Fintype.card_fin] at h
    exact h
  have hker := kernel_finrank (ComplexCharacter.rho.comp q) (exists_nontrivial q hq)
  rw [Fintype.card_fin] at hker
  omega

/-- The same bound in the quantifier form of `Targets.DeficiencyZeroTarget`. -/
theorem deficiency_at_most_one :
    ∀ (m k : ℕ) (q : FreeGroup (Fin m) →* G), Function.Surjective q →
      (∃ v : Fin k → FreeGroup (Fin m), Subgroup.normalClosure (Set.range v) = q.ker) →
        m ≤ k + 1 := by
  rintro m k q hq ⟨v, hv⟩
  exact rank_le_succ m k q hq v hv

end D2RelationGap.DeficiencyBound
