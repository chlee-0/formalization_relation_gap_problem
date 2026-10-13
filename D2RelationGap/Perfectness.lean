import D2RelationGap.RelationModule
import Mathlib.Algebra.Group.Conj

/-! OpenAI's perfectness argument, in abelian images of the actual kernel.
Credit: A Counterexample to Wall's D(2) Problem (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
The group-power proof implements the same 26/15 annihilation and Bezout argument. -/
namespace D2RelationGap.Perfectness
open Targets RelationModule
open scoped commutatorElement
noncomputable section

theorem power_annihilator {H : Type*} [Group H] (u v b : H) (n : ℕ)
    (hu : u = b ^ n) (hvb : v * b * v⁻¹ = b ^ (n + 1)) (hc : Commute v u) :
    u ^ n = 1 := by
  have he : v * u * v⁻¹ = u ^ (n + 1) := by
    rw [hu, ← conj_pow, hvb, ← pow_mul, ← pow_mul, Nat.mul_comm (n + 1) n]
  have hf : v * u * v⁻¹ = u := by rw [hc.eq]; simp [mul_assoc]
  have hp : u ^ (n + 1) = u := he.symm.trans hf
  apply mul_right_cancel (b := u)
  simpa only [pow_succ, one_mul] using hp

theorem coprime_powers {H : Type*} [Group H] (u : H)
    (h26 : u ^ 26 = 1) (h15 : u ^ 15 = 1) : u = 1 := by
  have h286 : u ^ 286 = 1 := by
    change u ^ (26 * 11) = 1
    rw [pow_mul, h26, one_pow]
  have h285 : u ^ 285 = 1 := by
    change u ^ (15 * 19) = 1
    rw [pow_mul, h15, one_pow]
  have h : u ^ 285 * u = 1 := by
    rw [← pow_succ]
    exact h286
  simpa only [h285, one_mul] using h

theorem original_t1_mem : freeWord t1 ∈ N := by
  apply MonoidHom.mem_ker.mpr
  exact PresentedGroup.one_of_mem (by simp [quotientRelations])

theorem original_t2_mem : freeWord t2 ∈ N := by
  apply MonoidHom.mem_ker.mpr
  exact PresentedGroup.one_of_mem (by simp [quotientRelations])

theorem source_power_identities {H : Type*} [Group H] (f : F →* H)
    (hrels : ∀ r ∈ sourceRelations, f r = 1) :
    let u := f (freeWord t1)
    let v := f (freeWord t2)
    let a := f (FreeGroup.of .a1)
    let b := f (FreeGroup.of .a2)
    let s := f (FreeGroup.of .s)
    u = b ^ 26 ∧ v * b * v⁻¹ = b ^ 27 ∧ u * a * u⁻¹ = a ^ 16 ∧
      s * v * s⁻¹ = a ^ 15 ∧ v * b * v⁻¹ * b⁻¹ = u ∧
      u * a * u⁻¹ * a⁻¹ = s * v * s⁻¹ := by
  have h0 := traces_sound_of_relators f hrels (wordTraces[0]) (List.getElem_mem _)
  have h1 := traces_sound_of_relators f hrels (wordTraces[1]) (List.getElem_mem _)
  have h2 := traces_sound_of_relators f hrels (wordTraces[2]) (List.getElem_mem _)
  have h3 := traces_sound_of_relators f hrels (wordTraces[3]) (List.getElem_mem _)
  have h4 := traces_sound_of_relators f hrels (wordTraces[4]) (List.getElem_mem _)
  have h5 := traces_sound_of_relators f hrels (wordTraces[5]) (List.getElem_mem _)
  change f (freeWord t1) = f (freeWord (List.replicate 26 (pos .a2))) at h0
  change f (freeWord (t2 ++ [pos .a2] ++ inverseWord t2)) =
    f (freeWord (List.replicate 27 (pos .a2))) at h1
  change f (freeWord (t1 ++ [pos .a1] ++ inverseWord t1)) =
    f (freeWord (List.replicate 16 (pos .a1))) at h2
  change f (freeWord ([pos .s] ++ t2 ++ [neg .s])) =
    f (freeWord (List.replicate 15 (pos .a1))) at h3
  change f (freeWord (t2 ++ [pos .a2] ++ inverseWord t2 ++ [neg .a2])) =
    f (freeWord t1) at h4
  change f (freeWord (t1 ++ [pos .a1] ++ inverseWord t1 ++ [neg .a1])) =
    f (freeWord ([pos .s] ++ t2 ++ [neg .s])) at h5
  have hp (g : Gen) (n : ℕ) : f (freeWord (List.replicate n (pos g))) =
      f (FreeGroup.of g) ^ n := by simp [freeWord, freeLetter, pos]
  rw [hp] at h1 h2 h3
  refine ⟨h0.trans (hp _ _), ?_, ?_, ?_, ?_, ?_⟩
  · simpa [freeWord_append, freeWord_inverse, freeWord_cons, freeWord_nil,
      freeLetter, pos, neg, hp, mul_assoc] using h1
  · simpa [freeWord_append, freeWord_inverse, freeWord_cons, freeWord_nil,
      freeLetter, pos, neg, hp, mul_assoc] using h2
  · simpa [freeWord_append, freeWord_inverse, freeWord_cons, freeWord_nil,
      freeLetter, pos, neg, hp, mul_assoc] using h3
  · simpa [freeWord_append, freeWord_inverse, freeWord_cons, freeWord_nil,
      freeLetter, pos, neg, hp, mul_assoc] using h4
  · simpa [freeWord_append, freeWord_inverse, freeWord_cons, freeWord_nil,
      freeLetter, pos, neg, hp, mul_assoc] using h5

/-- Every abelian image of actual N is killed by a source-relator-respecting map.
The displayed hypothesis is actual image commutativity, not perfectness as an assumption. -/
theorem abelian_kernel_image_trivial {H : Type*} [Group H] (f : F →* H)
    (hrels : ∀ r ∈ sourceRelations, f r = 1)
    (hab : ∀ n m : N, Commute (f (n : F)) (f (m : F))) :
    f (freeWord t1) = 1 ∧ f (freeWord t2) = 1 := by
  let u := f (freeWord t1)
  let v := f (freeWord t2)
  let a := f (FreeGroup.of .a1)
  let b := f (FreeGroup.of .a2)
  let s := f (FreeGroup.of .s)
  have hi : u = b ^ 26 ∧ v * b * v⁻¹ = b ^ 27 ∧ u * a * u⁻¹ = a ^ 16 ∧
      s * v * s⁻¹ = a ^ 15 ∧ v * b * v⁻¹ * b⁻¹ = u ∧
        u * a * u⁻¹ * a⁻¹ = s * v * s⁻¹ := source_power_identities f hrels
  obtain ⟨hu, hvb, hua, hv, hub, hva⟩ := hi
  have huv : Commute v u := hab ⟨_, original_t2_mem⟩ ⟨_, original_t1_mem⟩
  have huc : Commute u (s * v * s⁻¹) := by
    have h := hab ⟨_, original_t1_mem⟩
      (RelationModule.conjugate (FreeGroup.of .s) ⟨_, original_t2_mem⟩)
    change Commute u (f (FreeGroup.of .s * freeWord t2 * (FreeGroup.of .s)⁻¹)) at h
    simpa only [map_mul, map_inv] using h
  have h26 : u ^ 26 = 1 := power_annihilator u v b 26 hu hvb huv
  have hc15 : (s * v * s⁻¹) ^ 15 = 1 := power_annihilator _ u a 15 hv hua huc
  have h15v : v ^ 15 = 1 := by
    rw [conj_pow] at hc15
    have he := congrArg (fun z => s⁻¹ * z * s) hc15
    simpa [mul_assoc] using he
  have hvbc : Commute v (b * v⁻¹ * b⁻¹) := by
    have h := hab ⟨_, original_t2_mem⟩
      (RelationModule.conjugate (FreeGroup.of .a2) (⟨_, original_t2_mem⟩ : N)⁻¹)
    change Commute v (f (FreeGroup.of .a2 * (freeWord t2)⁻¹ * (FreeGroup.of .a2)⁻¹)) at h
    simpa only [map_mul, map_inv] using h
  have h15u : u ^ 15 = 1 := by
    have he : (v * (b * v⁻¹ * b⁻¹)) ^ 15 = 1 := by
      rw [hvbc.mul_pow, conj_pow, inv_pow, h15v]
      simp
    rw [← hub]
    simpa only [mul_assoc] using he
  have hu1 : u = 1 := coprime_powers u h26 h15u
  have hv1 : v = 1 := by
    have he : s * v * s⁻¹ = 1 := by simpa [hu1] using hva.symm
    have hh := congrArg (fun z => s⁻¹ * z * s) he
    simpa [mul_assoc] using hh
  exact ⟨hu1, hv1⟩

/-- Exactly OpenAI's normal subgroup of the actual four-relator group P. -/
def K : Subgroup P := Subgroup.normalClosure {sourceMap (freeWord t1), sourceMap (freeWord t2)}

instance K_normal : K.Normal := by unfold K; infer_instance

theorem source_kernel_image_le : N ≤ K.comap sourceMap := by
  rw [original_kernel_eq]
  apply Subgroup.normalClosure_le_normal
  intro r hr
  rcases hr with hsource | hlast
  · change sourceMap r ∈ K
    rw [PresentedGroup.one_of_mem hsource]
    exact K.one_mem
  · rcases Set.mem_insert_iff.mp hlast with rfl | hr
    · exact Subgroup.subset_normalClosure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff.mp hr]
      exact Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Perfectness expressed as equality of the ambient commutator subgroup with actual K. -/
theorem K_perfect : ⁅K, K⁆ = K := by
  let q : P →* P ⧸ ⁅K, K⁆ := QuotientGroup.mk' ⁅K, K⁆
  have hab : ∀ n m : N, Commute (q (sourceMap (n : F))) (q (sourceMap (m : F))) := by
    intro n m
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.commutator_mem_commutator (source_kernel_image_le n.property)
        (source_kernel_image_le m.property))
  have hk := abelian_kernel_image_trivial (q.comp sourceMap)
    (fun r hr => by simp [PresentedGroup.one_of_mem hr]) hab
  apply le_antisymm (Subgroup.commutator_le_left K K)
  apply Subgroup.normalClosure_le_normal
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · exact (QuotientGroup.eq_one_iff _).mp hk.1
  · rw [Set.mem_singleton_iff.mp hp]
    exact (QuotientGroup.eq_one_iff _).mp hk.2

theorem class_commutator_mem (V : Submodule R RelationCarrier) (n m : N) :
    ⁅(n : F), (m : F)⁆ ∈ classKernel V := by
  refine ⟨(⁅n, m⁆ : N).property, ?_⟩
  change Additive.ofMul (Abelianization.of ⁅n, m⁆) ∈ V
  simp [commutatorElement_def]

/-- The four original relator classes span the actual canonical integral relation module. -/
theorem sourceClasses_span : Submodule.span R (Set.range sourceClass) = ⊤ := by
  let V := Submodule.span R (Set.range sourceClass)
  let H := classKernel V
  let q : F →* F ⧸ H := QuotientGroup.mk' H
  have hrels : ∀ r ∈ sourceRelations, q r = 1 := by
    intro r hr
    apply (QuotientGroup.eq_one_iff r).mpr
    simp only [sourceRelations, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals
      first
      | exact ⟨FoxSpan.sourceRelator_mem_kernel 0, Submodule.subset_span ⟨0, rfl⟩⟩
      | exact ⟨FoxSpan.sourceRelator_mem_kernel 1, Submodule.subset_span ⟨1, rfl⟩⟩
      | exact ⟨FoxSpan.sourceRelator_mem_kernel 2, Submodule.subset_span ⟨2, rfl⟩⟩
      | exact ⟨FoxSpan.sourceRelator_mem_kernel 3, Submodule.subset_span ⟨3, rfl⟩⟩
  have hab : ∀ n m : N, Commute (q (n : F)) (q (m : F)) := by
    intro n m
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (class_commutator_mem V n m)
  have hk := abelian_kernel_image_trivial q hrels hab
  have hN : N ≤ H := by
    rw [original_kernel_eq]
    apply Subgroup.normalClosure_le_normal
    intro r hr
    rcases hr with hs | hl
    · exact (QuotientGroup.eq_one_iff _).mp (hrels r hs)
    · rcases Set.mem_insert_iff.mp hl with rfl | hl
      · exact (QuotientGroup.eq_one_iff _).mp hk.1
      · rw [Set.mem_singleton_iff.mp hl]
        exact (QuotientGroup.eq_one_iff _).mp hk.2
  apply Submodule.eq_top_iff'.mpr
  change ∀ v : Abelianization N, Additive.ofMul v ∈ V
  intro v
  refine QuotientGroup.induction_on v (fun n => ?_)
  obtain ⟨_, hcn⟩ := hN n.property
  exact hcn

theorem hasModuleGenerators_four : HasModuleGenerators (S := R) (V := RelationCarrier) 4 :=
  ⟨sourceClass, sourceClasses_span⟩

/-- Exact integral module generator count, separate from normal minimality and topology. -/
theorem integral_module_rank_four :
    HasModuleGenerators (S := R) (V := RelationCarrier) 4 ∧
      ∀ k, HasModuleGenerators (S := R) (V := RelationCarrier) k → 4 ≤ k :=
  ⟨hasModuleGenerators_four, fun _ => module_generators_at_least_four⟩

theorem K_commutator_eq_top : commutator K = ⊤ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_subtype_commutator, K_perfect, Subgroup.map_top, Subgroup.range_subtype]

theorem source_kernel_image_eq : N.map sourceMap = K := by
  have hn : (N.map sourceMap).Normal := Subgroup.Normal.map inferInstance sourceMap
    (PresentedGroup.mk_surjective sourceRelations)
  have := hn
  apply le_antisymm (Subgroup.map_le_iff_le_comap.mpr source_kernel_image_le)
  apply Subgroup.normalClosure_le_normal
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · exact Subgroup.mem_map_of_mem sourceMap original_t1_mem
  · rw [Set.mem_singleton_iff.mp hp]
    exact Subgroup.mem_map_of_mem sourceMap original_t2_mem

def R0 : Subgroup F := Subgroup.normalClosure sourceRelations

theorem sourceMap_kernel : sourceMap.ker = R0 := by
  ext f
  exact PresentedGroup.mk_eq_one_iff

def kernelToK : N →* K where
  toFun n := ⟨sourceMap (n : F), source_kernel_image_le n.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem kernelToK_surjective : Function.Surjective kernelToK := by
  intro k
  have hk : (k : P) ∈ N.map sourceMap := by rw [source_kernel_image_eq]; exact k.property
  obtain ⟨n, hn, he⟩ := hk
  exact ⟨⟨n, hn⟩, Subtype.ext he⟩

theorem kernelToK_kernel : kernelToK.ker = R0.subgroupOf N := by
  ext n
  change kernelToK n = 1 ↔ (n : F) ∈ R0
  rw [← sourceMap_kernel]
  change kernelToK n = 1 ↔ sourceMap (n : F) = 1
  exact Subtype.ext_iff

instance R0_in_kernel_normal : (R0.subgroupOf N).Normal := by
  rw [← kernelToK_kernel]
  infer_instance

/-- The actual quotient N/R0 is identified with actual K, with the natural map. -/
def kernelQuotientEquiv : N ⧸ R0.subgroupOf N ≃* K :=
  QuotientGroup.liftEquiv (R0.subgroupOf N) kernelToK_surjective kernelToK_kernel.symm

theorem kernelQuotientEquiv_of (n : N) : kernelQuotientEquiv (QuotientGroup.mk n) = kernelToK n := rfl

/-- Removing a source class from the generating family is rejected. -/
theorem corrupted_three_source_classes_rejected :
    Submodule.span R (Set.range (fun i : Fin 3 => sourceClass i.castSucc)) ≠ ⊤ := by
  intro h
  have he := module_generators_at_least_four ⟨_, h⟩
  omega

end
end D2RelationGap.Perfectness
