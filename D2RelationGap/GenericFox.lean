import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Evaluated left Fox calculus on an ARBITRARY free group with an arbitrary character
into a field: the cocycle laws, uniqueness of cocycles with prescribed generator
values, the fundamental identity, the chain rule along homomorphisms, normal
generation of spans, and the presentation-independence of the degree-one kernel
(`kernel_transfer`). This is standard Fox calculus; it is used to compare an
arbitrary finite epimorphism onto OpenAI's G with the fixed rank-five one.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies G and rho.
-/
noncomputable section
namespace D2RelationGap.GenericFox

section Affine
variable (ι K : Type*) [Field K]

@[ext] structure Affine where
  scalar : Kˣ
  vector : ι → K

variable {ι K}

instance : One (Affine ι K) := ⟨⟨1, 0⟩⟩
instance : Mul (Affine ι K) := ⟨fun a b =>
  ⟨a.scalar * b.scalar, fun g => a.vector g + (a.scalar : K) * b.vector g⟩⟩
instance : Inv (Affine ι K) := ⟨fun a =>
  ⟨a.scalar⁻¹, fun g => -(↑(a.scalar⁻¹) : K) * a.vector g⟩⟩

instance : Group (Affine ι K) where
  mul_assoc a b c := by
    apply Affine.ext
    · exact mul_assoc _ _ _
    · funext g
      change (a.vector g + (a.scalar : K) * b.vector g) +
        ↑(a.scalar * b.scalar) * c.vector g =
        a.vector g + (a.scalar : K) * (b.vector g + (b.scalar : K) * c.vector g)
      simp [mul_add, mul_assoc, add_assoc]
  one_mul a := by
    apply Affine.ext
    · exact one_mul _
    · funext g; change 0 + (↑(1 : Kˣ) : K) * a.vector g = a.vector g; simp
  mul_one a := by
    apply Affine.ext
    · exact mul_one _
    · funext g; change a.vector g + (a.scalar : K) * 0 = a.vector g; simp
  inv_mul_cancel a := by
    apply Affine.ext
    · exact inv_mul_cancel _
    · funext g; change -(a.scalar⁻¹ : Kˣ) * a.vector g +
        (a.scalar⁻¹ : Kˣ) * a.vector g = 0; simp

def scalarHom : Affine ι K →* Kˣ where
  toFun := Affine.scalar
  map_one' := rfl
  map_mul' _ _ := rfl

end Affine

variable {ι κ K : Type*} [DecidableEq ι] [DecidableEq κ] [Field K]

/-- The units-valued version of a character on a group. -/
def unitsChar (χ : FreeGroup ι →* K) : FreeGroup ι →* Kˣ := MonoidHom.toHomUnits χ

omit [DecidableEq ι] in
theorem unitsChar_val (χ : FreeGroup ι →* K) (f : FreeGroup ι) : (unitsChar χ f : K) = χ f := rfl

def lift (χ : FreeGroup ι →* K) : FreeGroup ι →* Affine ι K :=
  FreeGroup.lift (fun g => ⟨unitsChar χ (FreeGroup.of g), Pi.single g 1⟩)

/-- The evaluated left Fox derivative for the character χ. -/
def D (χ : FreeGroup ι →* K) (f : FreeGroup ι) : ι → K := (lift χ f).vector

theorem lift_scalar (χ : FreeGroup ι →* K) (f : FreeGroup ι) : (lift χ f).scalar = unitsChar χ f := by
  have h : scalarHom.comp (lift χ) = unitsChar χ :=
    FreeGroup.ext_hom _ _ (fun g => by simp [lift, scalarHom])
  exact DFunLike.congr_fun h f

theorem D_mul (χ : FreeGroup ι →* K) (u v : FreeGroup ι) : D χ (u * v) = D χ u + χ u • D χ v := by
  funext g
  simp only [D, map_mul]
  change (lift χ u).vector g + ((lift χ u).scalar : K) * (lift χ v).vector g = _
  rw [lift_scalar]; rfl

@[simp] theorem D_one (χ : FreeGroup ι →* K) : D χ 1 = 0 := by
  change (lift χ 1).vector = 0
  rw [map_one]; rfl

@[simp] theorem D_of (χ : FreeGroup ι →* K) (g : ι) : D χ (FreeGroup.of g) = Pi.single g 1 := by
  simp [D, lift]

omit [DecidableEq ι] in
theorem char_mul_inv (χ : FreeGroup ι →* K) (u : FreeGroup ι) : χ u * χ u⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem D_inv (χ : FreeGroup ι →* K) (u : FreeGroup ι) : D χ u⁻¹ = -(χ u⁻¹ • D χ u) := by
  have h := D_mul χ u⁻¹ u
  rw [inv_mul_cancel, D_one] at h
  rw [eq_neg_iff_add_eq_zero]
  exact h.symm

theorem D_conj (χ : FreeGroup ι →* K) (f n : FreeGroup ι) (hn : χ n = 1) :
    D χ (f * n * f⁻¹) = χ f • D χ n := by
  rw [D_mul, D_mul, map_mul, hn, mul_one, D_inv, smul_neg, smul_smul, char_mul_inv, one_smul]
  abel

omit [DecidableEq ι] in
/-- Two χ-cocycles with the same generator values coincide. -/
theorem cocycle_unique {V : Type*} [AddCommGroup V] [Module K V] (χ : FreeGroup ι →* K)
    (E E' : FreeGroup ι → V)
    (hE : ∀ u v, E (u * v) = E u + χ u • E v) (hE' : ∀ u v, E' (u * v) = E' u + χ u • E' v)
    (hg : ∀ g, E (FreeGroup.of g) = E' (FreeGroup.of g)) : E = E' := by
  have one : ∀ (X : FreeGroup ι → V), (∀ u v, X (u * v) = X u + χ u • X v) → X 1 = 0 := by
    intro X hX
    have h := hX 1 1
    rw [mul_one, map_one, one_smul] at h
    simpa using h
  have inv : ∀ (X : FreeGroup ι → V), (∀ u v, X (u * v) = X u + χ u • X v) →
      ∀ u, X u⁻¹ = -(χ u⁻¹ • X u) := by
    intro X hX u
    have h := hX u⁻¹ u
    rw [inv_mul_cancel, one X hX] at h
    rw [eq_neg_iff_add_eq_zero]
    exact h.symm
  funext f
  induction f using FreeGroup.induction_on with
  | one => rw [one E hE, one E' hE']
  | of g => exact hg g
  | inv_of g _ => rw [inv E hE, inv E' hE', hg]
  | mul a b ha hb => rw [hE, hE', ha, hb]

theorem D_unique (χ : FreeGroup ι →* K) (E : FreeGroup ι → ι → K)
    (hE : ∀ u v, E (u * v) = E u + χ u • E v) (hg : ∀ g, E (FreeGroup.of g) = Pi.single g 1) :
    E = D χ :=
  cocycle_unique χ E (D χ) hE (D_mul χ) (fun g => by rw [hg, D_of])

section Finite
variable [Fintype ι] [Fintype κ]

/-- The degree-one evaluated boundary. -/
def boundaryOne (χ : FreeGroup ι →* K) : (ι → K) →ₗ[K] K where
  toFun x := ∑ g, x g * (χ (FreeGroup.of g) - 1)
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_assoc, Finset.mul_sum]

theorem fundamental (χ : FreeGroup ι →* K) (f : FreeGroup ι) :
    boundaryOne χ (D χ f) = χ f - 1 := by
  have h := cocycle_unique (V := K) χ (fun f => boundaryOne χ (D χ f)) (fun f => χ f - 1)
    (fun u v => by simp only [D_mul, map_add, map_smul, smul_eq_mul])
    (fun u v => by simp only [map_mul, smul_eq_mul]; ring)
    (fun g => by simp [boundaryOne, Pi.single_apply])
  exact congrFun h f

omit [Fintype κ] in
/-- Fox chain rule along a homomorphism of free groups compatible with the characters. -/
theorem chain_rule (χ : FreeGroup ι →* K) (χ' : FreeGroup κ →* K)
    (φ : FreeGroup ι →* FreeGroup κ) (hφ : χ'.comp φ = χ) (f : FreeGroup ι) :
    D χ' (φ f) = ∑ i, D χ f i • D χ' (φ (FreeGroup.of i)) := by
  have hc : ∀ u, χ' (φ u) = χ u := fun u => DFunLike.congr_fun hφ u
  have h := cocycle_unique (V := κ → K) χ (fun f => D χ' (φ f))
    (fun f => ∑ i, D χ f i • D χ' (φ (FreeGroup.of i)))
    (fun u v => by rw [map_mul, D_mul, hc])
    (fun u v => by
      simp only [D_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
        Finset.smul_sum, smul_smul])
    (fun g => by
      simp only [D_of, Pi.single_apply, ite_smul, one_smul, zero_smul]
      simp)
  exact congrFun h f

/-- Elements of a subgroup on which χ is trivial and D lands in V. -/
def spanKernel (χ : FreeGroup ι →* K) (V : Submodule K (ι → K)) : Subgroup (FreeGroup ι) where
  carrier := {f | χ f = 1 ∧ D χ f ∈ V}
  one_mem' := ⟨map_one χ, by simp⟩
  mul_mem' := by
    rintro u v ⟨hu, hdu⟩ ⟨hv, hdv⟩
    refine ⟨by rw [map_mul, hu, hv, one_mul], ?_⟩
    rw [D_mul]
    exact V.add_mem hdu (V.smul_mem _ hdv)
  inv_mem' := by
    rintro u ⟨hu, hdu⟩
    refine ⟨by rw [map_inv, hu, inv_one], ?_⟩
    rw [D_inv]
    exact V.neg_mem (V.smul_mem _ hdu)

instance spanKernel_normal (χ : FreeGroup ι →* K) (V : Submodule K (ι → K)) :
    (spanKernel χ V).Normal where
  conj_mem := by
    rintro n ⟨hn, hdn⟩ f
    refine ⟨by rw [map_mul, map_mul, hn, mul_one, ← map_mul, mul_inv_cancel, map_one], ?_⟩
    rw [D_conj χ f n hn]
    exact V.smul_mem _ hdn

omit [Fintype ι] in
/-- Fox vectors of a normal closure lie in the span of the generators' Fox vectors. -/
theorem normalClosure_span (χ : FreeGroup ι →* K) {k : ℕ} (v : Fin k → FreeGroup ι)
    (hv : ∀ j, χ (v j) = 1) (n : FreeGroup ι) (hn : n ∈ Subgroup.normalClosure (Set.range v)) :
    D χ n ∈ Submodule.span K (Set.range (fun j => D χ (v j))) := by
  have h : Subgroup.normalClosure (Set.range v) ≤
      spanKernel χ (Submodule.span K (Set.range (fun j => D χ (v j)))) := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    exact ⟨hv j, Submodule.subset_span ⟨j, rfl⟩⟩
  exact (h hn).2

/-- The Fox span of a subgroup. -/
def foxSpan (χ : FreeGroup ι →* K) (H : Subgroup (FreeGroup ι)) : Submodule K (ι → K) :=
  Submodule.span K (D χ '' (H : Set (FreeGroup ι)))

/-- Presentation-independence of the degree-one kernel: if it is spanned by Fox vectors
of `Hi` for one free presentation, the same holds for any other compatible one. -/
theorem kernel_transfer (χ : FreeGroup ι →* K) (χ' : FreeGroup κ →* K)
    (Hi : Subgroup (FreeGroup ι)) (Hk : Subgroup (FreeGroup κ))
    (α : FreeGroup ι →* FreeGroup κ) (β : FreeGroup κ →* FreeGroup ι)
    (hα : χ'.comp α = χ) (hβ : χ.comp β = χ')
    (hαH : ∀ n ∈ Hi, α n ∈ Hk)
    (hround : ∀ i, (α (β (FreeGroup.of i)))⁻¹ * FreeGroup.of i ∈ Hk)
    (hker : LinearMap.ker (boundaryOne χ) ≤ foxSpan χ Hi) :
    LinearMap.ker (boundaryOne χ') ≤ foxSpan χ' Hk := by
  intro x hx
  let Ψ : (ι → K) →ₗ[K] (κ → K) :=
    Fintype.linearCombination K (fun g => D χ' (α (FreeGroup.of g)))
  have hΨ : ∀ f, Ψ (D χ f) = D χ' (α f) := by
    intro f
    rw [chain_rule χ χ' α hα f]
    simp [Ψ, Fintype.linearCombination_apply]
  let y : ι → K := ∑ i, x i • D χ (β (FreeGroup.of i))
  have hy : y ∈ LinearMap.ker (boundaryOne χ) := by
    have hc : ∀ u, χ (β u) = χ' u := fun u => DFunLike.congr_fun hβ u
    rw [LinearMap.mem_ker, map_sum]
    simp only [map_smul, fundamental, hc, smul_eq_mul]
    have := LinearMap.mem_ker.mp hx
    simpa [boundaryOne] using this
  have hΨy : Ψ y ∈ foxSpan χ' Hk := by
    have hm : Submodule.map Ψ (foxSpan χ Hi) ≤ foxSpan χ' Hk := by
      rw [foxSpan, Submodule.map_span_le]
      rintro _ ⟨n, hn, rfl⟩
      rw [hΨ]
      exact Submodule.subset_span ⟨α n, hαH n hn, rfl⟩
    exact hm ⟨y, hker hy, rfl⟩
  have hdiff : ∀ i, Pi.single i 1 - Ψ (D χ (β (FreeGroup.of i))) ∈ foxSpan χ' Hk := by
    intro i
    rw [hΨ, ← D_of χ' i]
    set u := FreeGroup.of i
    set u' := α (β u)
    have hd : D χ' (u'⁻¹ * u) = χ' u'⁻¹ • (D χ' u - D χ' u') := by
      rw [D_mul, D_inv, smul_sub]
      abel
    have hmem : D χ' (u'⁻¹ * u) ∈ foxSpan χ' Hk := Submodule.subset_span ⟨_, hround i, rfl⟩
    rw [hd] at hmem
    have h2 := (foxSpan χ' Hk).smul_mem (χ' u') hmem
    rw [smul_smul, char_mul_inv, one_smul] at h2
    exact h2
  have hx' : x = (x - Ψ y) + Ψ y := by abel
  rw [hx']
  refine (foxSpan χ' Hk).add_mem ?_ hΨy
  have hexp : x - Ψ y = ∑ i, x i • (Pi.single i 1 - Ψ (D χ (β (FreeGroup.of i)))) := by
    simp only [y, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    congr 1
    ext g
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hexp]
  exact Submodule.sum_mem _ (fun i _ => (foxSpan χ' Hk).smul_mem _ (hdiff i))

/-- A nonzero degree-one boundary has kernel of dimension one less than the rank. -/
theorem kernel_finrank (χ : FreeGroup ι →* K) (h : ∃ g, χ (FreeGroup.of g) ≠ 1) :
    Module.finrank K (LinearMap.ker (boundaryOne χ)) + 1 = Fintype.card ι := by
  obtain ⟨g, hg⟩ := h
  have hs : Function.Surjective (boundaryOne χ) := by
    intro z
    refine ⟨(z / (χ (FreeGroup.of g) - 1)) • Pi.single g 1, ?_⟩
    have hne : χ (FreeGroup.of g) - 1 ≠ 0 := sub_ne_zero.mpr hg
    simp [boundaryOne, Pi.single_apply, div_mul_cancel₀ _ hne]
  have hr := (boundaryOne χ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hr
  omega

end Finite

end D2RelationGap.GenericFox
