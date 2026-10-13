import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
Abstract simplicial voltage complexes and actual images of height lifts.
OpenAI's "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, Section 2,
supplies the tower argument. This module does not assert its geometric or
local-system homology adapters, existence of a nonexact cocycle, or heights.
-/

noncomputable section
namespace D2RelationGap.SimplicialImages

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

def heightLift (f : U → V) (h : U → ℤ) (u : U) : V × ℤ := (f u, h u)

/-- Every pair of vertices of a lifted face has the prescribed height difference.
This defines an abstract complex even before a cocycle proves all base faces lift. -/
def voltageComplex (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ) :
    PreAbstractSimplicialComplex (V × ℤ) := by
  classical
  exact {
    faces := {s | s.Nonempty ∧ s.image Prod.fst ∈ A ∧
      ∀ x ∈ s, ∀ y ∈ s, y.2 - x.2 = a x.1 y.1}
    isRelLowerSet_faces := by
      intro s hs
      refine ⟨hs.1, ?_⟩
      intro t hts ht
      refine ⟨ht, ?_, ?_⟩
      · exact (A.isRelLowerSet_faces hs.2.1).2
          (Finset.image_subset_image hts) (Finset.image_nonempty.mpr ht)
      · intro x hx y hy
        exact hs.2.2 x (hts hx) y (hts hy) }

/-- The height constraint forces projection to be nondegenerate on each face. -/
theorem projection_injective_on_face (A : PreAbstractSimplicialComplex V)
    (a : V → V → ℤ) (s : Finset (V × ℤ))
    (hs : s ∈ voltageComplex A a) : Set.InjOn Prod.fst (s : Set (V × ℤ)) := by
  intro x hx y hy hxy
  have hh := hs.2.2 x hx y hy
  have hd := hs.2.2 y hy y hy
  simp only [sub_self] at hd
  rw [hxy, ← hd] at hh
  exact Prod.ext hxy (sub_eq_zero.mp hh).symm

def AtMostTwo (A : PreAbstractSimplicialComplex V) : Prop :=
  ∀ s ∈ A, s.card ≤ 3

theorem voltageComplex_atMostTwo (A : PreAbstractSimplicialComplex V)
    (a : V → V → ℤ) (hA : AtMostTwo A) :
    AtMostTwo (voltageComplex A a) := by
  classical
  intro s hs
  have hc := Finset.card_image_of_injOn (projection_injective_on_face A a s hs)
  exact hc ▸ hA (s.image Prod.fst) hs.2.1

omit [DecidableEq U] in
theorem image_atMostTwo (A : PreAbstractSimplicialComplex U) (f : U → V)
    (hA : AtMostTwo A) : AtMostTwo (by classical exact A.map f) := by
  classical
  rintro s ⟨t, ht, rfl⟩
  exact (Finset.card_image_le).trans (hA t ht)

/-- The finite-set image is an actual abstract subcomplex of the voltage complex.
Collapsed vertices and reordered images require no injectivity/order hypothesis on f. -/
theorem height_image_le_voltage (A : PreAbstractSimplicialComplex U) (f : U → V)
    (h : U → ℤ) (a : V → V → ℤ)
    (hh : ∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v)) :
    (by classical exact A.map (heightLift f h)) ≤
      voltageComplex (by classical exact A.map f) a := by
  classical
  rintro s ⟨t, ht, rfl⟩
  refine ⟨Finset.image_nonempty.mpr (A.isRelLowerSet_faces ht).1, ?_, ?_⟩
  · refine ⟨t, ht, ?_⟩
    simp [Finset.image_image, heightLift, Function.comp_def]
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    apply hh
    exact (A.isRelLowerSet_faces ht).2 (Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩)
      (Finset.insert_nonempty _ _)

/-- Actual vertices of the lifted image: the source has every singleton face. -/
abbrev ImageVertex (f : U → V) (h : U → ℤ) := Set.range (heightLift f h)

def toImageVertex (f : U → V) (h : U → ℤ) (u : U) : ImageVertex f h :=
  ⟨heightLift f h u, Set.mem_range_self u⟩

omit [DecidableEq U] [DecidableEq V] in
theorem toImageVertex_surjective (f : U → V) (h : U → ℤ) :
    Function.Surjective (toImageVertex f h) := by
  rintro ⟨x, u, rfl⟩
  exact ⟨u, rfl⟩

instance imageVertexFinite [Finite U] (f : U → V) (h : U → ℤ) :
    Finite (ImageVertex f h) := Finite.of_surjective _ (toImageVertex_surjective f h)

instance imageVertexFintype [Fintype U] (f : U → V) (h : U → ℤ) :
    Fintype (ImageVertex f h) := Fintype.ofFinite _

omit [DecidableEq U] in
theorem singleton_image_iff (A : AbstractSimplicialComplex U) (f : U → V)
    (h : U → ℤ) (x : V × ℤ) :
    (by classical exact ({x} : Finset (V × ℤ)) ∈
      A.toPreAbstractSimplicialComplex.map (heightLift f h)) ↔ x ∈ ImageVertex f h := by
  classical
  constructor
  · rintro ⟨s, hs, heq⟩
    change s.image (heightLift f h) = {x} at heq
    have hx : x ∈ s.image (heightLift f h) := by rw [heq]; simp
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨{u}, A.singleton_mem u, by simp⟩

def imageProjection (f : U → V) (h : U → ℤ) (x : ImageVertex f h) : V := x.val.1

omit [DecidableEq U] [DecidableEq V] in
theorem imageProjection_surjective (f : U → V) (h : U → ℤ)
    (hf : Function.Surjective f) : Function.Surjective (imageProjection f h) := by
  intro v
  obtain ⟨u, rfl⟩ := hf v
  exact ⟨toImageVertex f h u, rfl⟩

def ExactVoltage (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ) : Prop :=
  ∃ p : V → ℤ, ∀ u v, ({u, v} : Finset V) ∈ A → a u v = p v - p u

theorem exactVoltage_of_injective_imageProjection (A : PreAbstractSimplicialComplex U)
    (f : U → V) (h : U → ℤ) (a : V → V → ℤ) (hf : Function.Surjective f)
    (hh : ∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v))
    (hi : Function.Injective (imageProjection f h)) :
    ExactVoltage (by classical exact A.map f) a := by
  classical
  let s := Function.surjInv (imageProjection_surjective f h hf)
  have ps : ∀ v, imageProjection f h (s v) = v :=
    Function.rightInverse_surjInv _
  refine ⟨fun v => (s v).val.2, ?_⟩
  intro u v huv
  obtain ⟨t, ht, heq⟩ := huv
  change t.image f = {u, v} at heq
  have hu : u ∈ t.image f := by rw [heq]; simp
  have hv : v ∈ t.image f := by rw [heq]; simp
  obtain ⟨u', hu', hfu⟩ := Finset.mem_image.mp hu
  obtain ⟨v', hv', hfv⟩ := Finset.mem_image.mp hv
  have hpair : ({u', v'} : Finset U) ∈ A :=
    (A.isRelLowerSet_faces ht).2 (Finset.insert_subset_iff.mpr ⟨hu', Finset.singleton_subset_iff.mpr hv'⟩)
      (Finset.insert_nonempty _ _)
  have hs_u : s u = toImageVertex f h u' := hi ((ps u).trans hfu.symm)
  have hs_v : s v = toImageVertex f h v' := hi ((ps v).trans hfv.symm)
  change a u v = (s v).val.2 - (s u).val.2
  rw [hs_u, hs_v]
  simpa only [toImageVertex, heightLift, hfu, hfv] using (hh u' v' hpair).symm

/-- Growth and the bound by the SAME fixed source vertex set. Nonexactness and
the height equation remain explicit obligations, not assumed growth. -/
theorem strict_vertex_growth [Fintype U] [Fintype V]
    (A : AbstractSimplicialComplex U) (f : U → V) (h : U → ℤ) (a : V → V → ℤ)
    (hf : Function.Surjective f)
    (hh : ∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v))
    (ha : ¬ ExactVoltage (by classical exact A.toPreAbstractSimplicialComplex.map f) a) :
    Fintype.card V < Fintype.card (ImageVertex f h) ∧
      Fintype.card (ImageVertex f h) ≤ Fintype.card U := by
  classical
  have hp := imageProjection_surjective f h hf
  have hn : ¬ Function.Injective (imageProjection f h) := by
    intro hi
    exact ha (exactVoltage_of_injective_imageProjection A.toPreAbstractSimplicialComplex
      f h a hf hh hi)
  let s := Function.surjInv hp
  have hs := Function.injective_surjInv hp
  have hns : ¬ Function.Surjective s := by
    intro hsurj
    have hl := Function.leftInverse_of_surjective_of_rightInverse hsurj
      (Function.rightInverse_surjInv hp)
    exact hn hl.injective
  exact ⟨Fintype.card_lt_of_injective_not_surjective s hs hns,
    Fintype.card_le_of_surjective _ (toImageVertex_surjective f h)⟩

/-- Triangle flatness includes repeated vertices, hence antisymmetry and zero
diagonal on vertices of faces. Existence of this cocycle is not asserted. -/
def FlatVoltage (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ) : Prop :=
  ∀ r u v, ({r, u, v} : Finset V) ∈ A → a r u + a u v = a r v

/-- Every base face has a lift at every prescribed root height. This theorem
still concerns abstract simplicial complexes, not geometric covering spaces. -/
theorem face_lift_exists (A : PreAbstractSimplicialComplex V) (a : V → V → ℤ)
    (ha : FlatVoltage A a) (s : Finset V) (hs : s ∈ A) (r : V) (hr : r ∈ s)
    (n : ℤ) : ∃ t ∈ voltageComplex A a,
      t.image Prod.fst = s ∧ (r, n) ∈ t := by
  classical
  let g : V → V × ℤ := fun v => (v, n + a r v)
  have hflat : ∀ u ∈ s, ∀ v ∈ s, a r u + a u v = a r v := by
    intro u hu v hv
    apply ha
    exact (A.isRelLowerSet_faces hs).2
      (Finset.insert_subset_iff.mpr ⟨hr, Finset.insert_subset_iff.mpr
        ⟨hu, Finset.singleton_subset_iff.mpr hv⟩⟩) (Finset.insert_nonempty _ _)
  have hdiag : a r r = 0 := by
    have hh := hflat r hr r hr
    exact add_left_cancel (hh.trans (add_zero _).symm)
  refine ⟨s.image g, ?_, ?_, ?_⟩
  · refine ⟨Finset.image_nonempty.mpr (A.isRelLowerSet_faces hs).1, ?_, ?_⟩
    · simpa [Finset.image_image, g, Function.comp_def] using hs
    · intro x hx y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      change (n + a r v) - (n + a r u) = a u v
      exact (sub_eq_iff_eq_add).mpr (by
        rw [← hflat u hu v hv]
        ac_rfl)
  · simp [Finset.image_image, g, Function.comp_def]
  · apply Finset.mem_image.mpr
    exact ⟨r, hr, by simp [g, hdiag]⟩

/-- A nonzero exact voltage has a section and does not force vertex growth. -/
theorem nonzero_exact_voltage_no_growth :
    let h : Fin 2 → ℤ := fun u => u.val
    let a : Fin 2 → Fin 2 → ℤ := fun u v => h v - h u
    a 0 1 ≠ 0 ∧ ExactVoltage (⊤ : PreAbstractSimplicialComplex (Fin 2)) a ∧
      Fintype.card (ImageVertex (id : Fin 2 → Fin 2) h) = Fintype.card (Fin 2) := by
  dsimp only
  refine ⟨by decide, ⟨fun u => u.val, fun _ _ _ => rfl⟩, ?_⟩
  apply Fintype.card_eq.mpr
  exact ⟨(Equiv.ofBijective (toImageVertex id (fun u : Fin 2 => u.val))
    ⟨fun u v h => congrArg (fun x : ImageVertex id (fun u : Fin 2 => u.val) => x.val.1) h,
      toImageVertex_surjective _ _⟩).symm⟩

/-- A collapsed edge with unequal endpoint heights cannot be a simplicial lift. -/
theorem corrupted_collapsed_height_rejected :
    let A : PreAbstractSimplicialComplex (Fin 2) := ⊤
    let f : Fin 2 → Unit := fun _ => ()
    let h : Fin 2 → ℤ := fun u => u.val
    ¬ A.map (heightLift f h) ≤ voltageComplex (A.map f) (fun _ _ => 0) := by
  dsimp only
  intro hi
  let f : Fin 2 → Unit := fun _ => ()
  let h : Fin 2 → ℤ := fun u => u.val
  have hs := hi (show ({0, 1} : Finset (Fin 2)).image (heightLift f h) ∈
      (⊤ : PreAbstractSimplicialComplex (Fin 2)).map (heightLift f h) from
    ⟨{0, 1}, Finset.insert_nonempty _ _, rfl⟩)
  have hh := hs.2.2 (heightLift f h 0) (Finset.mem_image_of_mem _ (by simp))
    (heightLift f h 1) (Finset.mem_image_of_mem _ (by simp))
  norm_num [heightLift, f, h] at hh

end D2RelationGap.SimplicialImages
