import D2RelationGap.VoltageExistence
import D2RelationGap.OrderedVoltageCover

/-!
Admissibility of an actual tagged height image for supplied unit transport.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the tower.
Actual fixed-source exactness, presentation/character adequacy and geometric
local-system homology remain separate obligations. No full obstruction is asserted.
-/
noncomputable section
namespace D2RelationGap.LiftedImageStep
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops SimplicialImages
open IntegerHeights
variable {U V K : Type*} [LinearOrder U] [LinearOrder V] [Field K]

omit [LinearOrder U] in
/-- Active vertices of an actual image come from active source vertices,
even when an entire higher-dimensional face collapses to a singleton. -/
theorem image_vertex_surjective (A : PreAbstractSimplicialComplex U) (f : U → V) :
    Function.Surjective (mapVertex f (le_refl (A.map f))) := by
  rintro ⟨v, hv⟩
  obtain ⟨s, hs, he⟩ := hv
  change s.image f = {v} at he
  have hv' : v ∈ s.image f := by rw [he]; simp
  obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hv'
  refine ⟨⟨u, vertex_mem_of_face A s hs u hu⟩, ?_⟩
  exact Subtype.ext hfu

def imagePaths (A : PreAbstractSimplicialComplex U) (f : U → V) (r : Vertex A)
    (paths : ∀ u : Vertex A, Path A r.val u.val) :
    ∀ v : Vertex (A.map f), Path (A.map f) (f r.val) v.val := by
  intro v
  let u := Classical.choose (image_vertex_surjective A f v)
  have hu := Classical.choose_spec (image_vertex_surjective A f v)
  have hp := mapPath f (le_refl (A.map f)) (paths u)
  have he : f u.val = v.val := congrArg Subtype.val hu
  exact he ▸ hp

omit [LinearOrder U] in
theorem image_vertices_finite (A : PreAbstractSimplicialComplex U) (f : U → V)
    [Finite (Vertex A)] : Finite (Vertex (A.map f)) :=
  Finite.of_surjective _ (image_vertex_surjective A f)

theorem edges_finite (A : PreAbstractSimplicialComplex V) [Finite (Vertex A)] :
    Finite (Edge A) := by
  let enc : Edge A → Vertex A × Vertex A := fun e =>
    (⟨e.src, vertex_mem_of_face A _ e.face e.src (by simp)⟩,
     ⟨e.dst, vertex_mem_of_face A _ e.face e.dst (by simp)⟩)
  apply Finite.of_injective enc
  intro e d he
  exact Edge.ext (congrArg (fun x => x.1.val) he) (congrArg (fun x => x.2.val) he)

theorem triangles_finite (A : PreAbstractSimplicialComplex V) [Finite (Vertex A)] :
    Finite (Triangle A) := by
  let enc : Triangle A → Vertex A × Vertex A × Vertex A := fun t =>
    (⟨t.v0, vertex_mem_of_face A _ t.face t.v0 (by simp)⟩,
     ⟨t.v1, vertex_mem_of_face A _ t.face t.v1 (by simp)⟩,
     ⟨t.v2, vertex_mem_of_face A _ t.face t.v2 (by simp)⟩)
  apply Finite.of_injective enc
  intro t s he
  exact Triangle.ext (congrArg (fun x => x.1.val) he)
    (congrArg (fun x => x.2.1.val) he) (congrArg (fun x => x.2.2.val) he)

def lift (f : U → V) (h : U → ℤ) (u : U) : V ×ₗ ℤ := toLex (heightLift f h u)
def image (A : PreAbstractSimplicialComplex U) (f : U → V) (h : U → ℤ) := A.map (lift f h)
def projection (x : V ×ₗ ℤ) : V := (ofLex x).1

omit [LinearOrder U] in
theorem image_projection (A : PreAbstractSimplicialComplex U) (f : U → V) (h : U → ℤ) :
    (image A f h).map projection ≤ A.map f := by
  rintro s ⟨t, ⟨q, hq, rfl⟩, rfl⟩
  refine ⟨q, hq, ?_⟩
  simp [Finset.image_image, Function.comp_def, projection, lift, heightLift]

def imageTransport (A : PreAbstractSimplicialComplex U) (f : U → V) (h : U → ℤ)
    (tau : Transport (K := K) (A.map f)) : Transport (K := K) (image A f h) :=
  pullback tau projection (image_projection A f h)

omit [LinearOrder U] in
theorem image_coeff (A : PreAbstractSimplicialComplex U) (f : U → V) (h : U → ℤ)
    (tau : Transport (K := K) (A.map f)) :
    coeff (imageTransport A f h tau) = OrderedVoltageCover.pullTransport (coeff tau) := rfl

theorem source_pullback (A : PreAbstractSimplicialComplex U) (f : U → V) (h : U → ℤ)
    (tau : Transport (K := K) (A.map f)) :
    pullback (imageTransport A f h tau) (lift f h) (le_refl (image A f h)) =
      pullback tau f (le_refl (A.map f)) := rfl

theorem image_holonomy (A : PreAbstractSimplicialComplex U) (f : U → V) (h : U → ℤ)
    (tau : Transport (K := K) (A.map f)) (r : Vertex A) (c : Loop A r) :
    holonomy (imageTransport A f h tau) (mapVertex (lift f h) (le_refl _) r)
      (BasedLoops.map (lift f h) (le_refl _) r c) =
      holonomy (pullback tau f (le_refl _)) r c := by
  have hn := congrArg (fun hom => hom c)
    (holonomy_natural (imageTransport A f h tau) (lift f h) (le_refl _) r)
  dsimp [imageTransport, pullback, lift, projection, heightLift, holonomy,
    BasedLoops.map, MonoidHom.comp] at hn ⊢
  exact hn

theorem image_two_injective (A : PreAbstractSimplicialComplex U) (f : U → V)
    (h : U → ℤ) (a : V → V → ℤ) (ha : FlatVoltage (A.map f) a)
    (hh : ∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v))
    (tau : Transport (K := K) (A.map f))
    [Fintype (Edge (A.map f))] [Fintype (Triangle (A.map f))]
    (h2 : Function.Injective (boundaryTwo (A.map f) (coeff tau))) :
    Function.Injective (boundaryTwo (image A f h) (coeff (imageTransport A f h tau))) :=
  OrderedVoltageCover.height_image_two_injective A f h a ha hh (coeff tau) h2

/-- Constructs voltage and heights from actual chain hypotheses. The next image
has the same nontrivial source-loop holonomy and injective degree-two boundary.
Neither condition on the image is an input. -/
theorem exists_admissible_image (A : PreAbstractSimplicialComplex U) (f : U → V)
    [Fintype (Vertex (A.map f))] [Fintype (Edge (A.map f))]
    [Fintype (Triangle (A.map f))] (tau : Transport (K := K) (A.map f))
    (r : Vertex A) (paths : ∀ u : Vertex A, Path A r.val u.val) (c : Loop A r)
    (hc : holonomy (pullback tau f (le_refl _)) r c ≠ 1)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker)
    (h2 : Function.Injective (boundaryTwo (A.map f) (coeff tau))) :
    ∃ (a : V → V → ℤ) (h : U → ℤ), FlatVoltage (A.map f) a ∧
      ¬ ExactVoltage (A.map f) a ∧
      (∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v)) ∧
      image A f h ≤ OrderedVoltageCover.cover (A.map f) a ∧
      Function.Injective (boundaryTwo (image A f h) (coeff (imageTransport A f h tau))) ∧
      holonomy (imageTransport A f h tau) (mapVertex (lift f h) (le_refl _) r)
        (BasedLoops.map (lift f h) (le_refl _) r c) ≠ 1 := by
  have hc' : holonomy tau (mapVertex f (le_refl _) r)
      (BasedLoops.map f (le_refl _) r c) ≠ 1 := by
    simpa only [← MonoidHom.comp_apply, holonomy_natural] using hc
  obtain ⟨a, ha, hne⟩ := VoltageExistence.exists_voltage_from_holonomy (A.map f) tau
    (mapVertex f (le_refl _) r) (imagePaths A f r paths)
    (BasedLoops.map f (le_refl _) r c) hc' h2
  obtain ⟨h, hh⟩ := pullback_height f (le_refl _) a ha r paths hex
  exact ⟨a, h, ha, hne, hh, OrderedVoltageCover.height_image_le_cover A f h a hh,
    image_two_injective A f h a ha hh tau h2, by rw [image_holonomy]; exact hc⟩

/-- Finiteness and connectedness of the actual image are derived from the
fixed source. Applying the rank/voltage theorem again needs no new holonomy input. -/
theorem image_has_next_voltage (A : PreAbstractSimplicialComplex U) (f : U → V)
    [Finite (Vertex A)] (h : U → ℤ) (tau : Transport (K := K) (A.map f))
    (r : Vertex A) (paths : ∀ u : Vertex A, Path A r.val u.val) (c : Loop A r)
    (hc : holonomy (pullback tau f (le_refl _)) r c ≠ 1)
    (h2 : Function.Injective (boundaryTwo (image A f h) (coeff (imageTransport A f h tau)))) :
    ∃ b : (V ×ₗ ℤ) → (V ×ₗ ℤ) → ℤ,
      FlatVoltage (image A f h) b ∧ ¬ ExactVoltage (image A f h) b := by
  have : Finite (Vertex (image A f h)) := image_vertices_finite A (lift f h)
  have : Finite (Edge (image A f h)) := edges_finite (image A f h)
  have : Finite (Triangle (image A f h)) := triangles_finite (image A f h)
  let : Fintype (Vertex (image A f h)) := Fintype.ofFinite _
  let : Fintype (Edge (image A f h)) := Fintype.ofFinite _
  let : Fintype (Triangle (image A f h)) := Fintype.ofFinite _
  apply VoltageExistence.exists_voltage_from_holonomy (image A f h)
    (imageTransport A f h tau) (mapVertex (lift f h) (le_refl _) r)
    (imagePaths A (lift f h) r paths) (BasedLoops.map (lift f h) (le_refl _) r c) _ h2
  rw [image_holonomy]
  exact hc

def imageVertexEquiv (A : AbstractSimplicialComplex U) (f : U → V) (h : U → ℤ) :
    Vertex (image A.toPreAbstractSimplicialComplex f h) ≃ ImageVertex f h where
  toFun x := ⟨ofLex x.val, by
    obtain ⟨u, hu⟩ := image_vertex_surjective A.toPreAbstractSimplicialComplex (lift f h) x
    refine ⟨u.val, ?_⟩
    have he := congrArg (fun y => ofLex y.val) hu
    exact he⟩
  invFun x := ⟨toLex x.val, by
    obtain ⟨u, hu⟩ := x.property
    refine ⟨{u}, A.singleton_mem u, ?_⟩
    simp [lift, hu]⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl

omit [LinearOrder U] in
theorem image_vertex_card (A : AbstractSimplicialComplex U) (f : U → V) (h : U → ℤ)
    [Fintype U] : Nat.card (Vertex (image A.toPreAbstractSimplicialComplex f h)) =
      Fintype.card (ImageVertex f h) := by
  rw [Nat.card_congr (imageVertexEquiv A f h), Nat.card_eq_fintype_card]

/-- The cardinality is that of actual active vertices of this SAME tagged image. -/
theorem image_vertex_growth (A : AbstractSimplicialComplex U) (f : U → V) (h : U → ℤ)
    (a : V → V → ℤ) [Fintype U] [Fintype V] (hf : Function.Surjective f)
    (hh : ∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v))
    (hne : ¬ ExactVoltage (A.toPreAbstractSimplicialComplex.map f) a) :
    Fintype.card V < Nat.card (Vertex (image A.toPreAbstractSimplicialComplex f h)) ∧
      Nat.card (Vertex (image A.toPreAbstractSimplicialComplex f h)) ≤ Fintype.card U := by
  rw [image_vertex_card]
  exact strict_vertex_growth A f h a hf hh hne

/-- Projection between the actual ACTIVE vertex sets; the ambient types may be infinite. -/
def activeProjection (A : PreAbstractSimplicialComplex U) (f : U → V) (h : U → ℤ) :
    Vertex (image A f h) → Vertex (A.map f) :=
  mapVertex projection (image_projection A f h)

omit [LinearOrder U] in
theorem activeProjection_surjective (A : PreAbstractSimplicialComplex U)
    (f : U → V) (h : U → ℤ) : Function.Surjective (activeProjection A f h) := by
  intro v
  obtain ⟨u, hu⟩ := image_vertex_surjective A f v
  refine ⟨mapVertex (lift f h) (le_refl _) u, ?_⟩
  exact hu

/-- If every active base vertex has only one height, edge-surjectivity forces
an actual vertex potential. Neither ambient surjectivity nor ambient finiteness is used. -/
theorem exact_of_injective_activeProjection (A : PreAbstractSimplicialComplex U)
    (f : U → V) (h : U → ℤ) (a : V → V → ℤ)
    (hh : ∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v))
    (hi : Function.Injective (activeProjection A f h)) : ExactVoltage (A.map f) a := by
  classical
  let sec := Function.surjInv (activeProjection_surjective A f h)
  have hs : ∀ v, activeProjection A f h (sec v) = v := Function.rightInverse_surjInv _
  let potential (v : V) : ℤ :=
    if hv : ({v} : Finset V) ∈ A.map f then (ofLex (sec ⟨v, hv⟩).val).2 else 0
  have hp (u : Vertex A) : potential (f u.val) = h u.val := by
    let b := mapVertex f (le_refl (A.map f)) u
    let q := mapVertex (lift f h) (le_refl (image A f h)) u
    have he : sec b = q := hi (hs b)
    have hb : ({f u.val} : Finset V) ∈ A.map f := b.property
    dsimp only [potential]
    rw [dite_eq_left hb]
    change (ofLex (sec b).val).2 = h u.val
    rw [he]
    rfl
  refine ⟨potential, ?_⟩
  intro u v huv
  obtain ⟨t, ht, he⟩ := huv
  change t.image f = {u, v} at he
  have hu : u ∈ t.image f := by rw [he]; simp
  have hv : v ∈ t.image f := by rw [he]; simp
  obtain ⟨u', hu', hfu⟩ := Finset.mem_image.mp hu
  obtain ⟨v', hv', hfv⟩ := Finset.mem_image.mp hv
  let su : Vertex A := ⟨u', vertex_mem_of_face A t ht u' hu'⟩
  let sv : Vertex A := ⟨v', vertex_mem_of_face A t ht v' hv'⟩
  have hpair := pair_mem_of_face A t ht u' v' hu' hv'
  have hh' := hh u' v' hpair
  rw [← hfu, ← hfv, hp su, hp sv]
  exact hh'.symm

/-- Counts only finite ACTIVE vertices, including when either ambient type is infinite. -/
theorem active_vertex_growth (A : PreAbstractSimplicialComplex U) (f : U → V)
    [Finite (Vertex A)] (h : U → ℤ) (a : V → V → ℤ)
    (hh : ∀ u v, ({u, v} : Finset U) ∈ A → h v - h u = a (f u) (f v))
    (hne : ¬ ExactVoltage (A.map f) a) :
    Nat.card (Vertex (A.map f)) < Nat.card (Vertex (image A f h)) ∧
      Nat.card (Vertex (image A f h)) ≤ Nat.card (Vertex A) := by
  have : Finite (Vertex (A.map f)) := image_vertices_finite A f
  have : Finite (Vertex (image A f h)) := image_vertices_finite A (lift f h)
  let : Fintype (Vertex (A.map f)) := Fintype.ofFinite _
  let : Fintype (Vertex (image A f h)) := Fintype.ofFinite _
  have hp := activeProjection_surjective A f h
  have hn : ¬ Function.Injective (activeProjection A f h) :=
    fun hi => hne (exact_of_injective_activeProjection A f h a hh hi)
  let sec := Function.surjInv hp
  have hi := Function.injective_surjInv hp
  have hns : ¬ Function.Surjective sec := by
    intro hsurj
    exact hn (Function.leftInverse_of_surjective_of_rightInverse hsurj
      (Function.rightInverse_surjInv hp)).injective
  refine ⟨?_, Nat.card_le_card_of_surjective _ (image_vertex_surjective A (lift f h))⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective sec hi hns

/-- One fixed source, with no finite ambient base or ambient surjectivity hypothesis. -/
theorem exists_growing_admissible_image (A : PreAbstractSimplicialComplex U) (f : U → V)
    [Finite (Vertex A)] (tau : Transport (K := K) (A.map f))
    (r : Vertex A) (paths : ∀ u : Vertex A, Path A r.val u.val) (c : Loop A r)
    (hc : holonomy (pullback tau f (le_refl _)) r c ≠ 1)
    (hex : (ordinaryTwo A).range = (ordinaryOne A).ker)
    (h2 : Function.Injective (boundaryTwo (A.map f) (coeff tau))) :
    ∃ h : U → ℤ,
      Function.Injective (boundaryTwo (image A f h) (coeff (imageTransport A f h tau))) ∧
      holonomy (pullback (imageTransport A f h tau) (lift f h) (le_refl _)) r c ≠ 1 ∧
      Nat.card (Vertex (A.map f)) < Nat.card (Vertex (image A f h)) ∧
      Nat.card (Vertex (image A f h)) ≤ Nat.card (Vertex A) := by
  have : Finite (Vertex (A.map f)) := image_vertices_finite A f
  have : Finite (Edge (A.map f)) := edges_finite (A.map f)
  have : Finite (Triangle (A.map f)) := triangles_finite (A.map f)
  let : Fintype (Vertex (A.map f)) := Fintype.ofFinite _
  let : Fintype (Edge (A.map f)) := Fintype.ofFinite _
  let : Fintype (Triangle (A.map f)) := Fintype.ofFinite _
  obtain ⟨a, h, ha, hne, hh, _, h2', _⟩ := exists_admissible_image A f tau r paths c hc hex h2
  obtain ⟨hg, hb⟩ := active_vertex_growth A f h a hh hne
  exact ⟨h, h2', by rw [source_pullback]; exact hc, hg, hb⟩

theorem zero_height_projection_bijective (A : PreAbstractSimplicialComplex V) :
    Function.Bijective (activeProjection A (id : V → V) (fun _ => 0)) := by
  refine ⟨?_, activeProjection_surjective A id (fun _ => 0)⟩
  intro x y hxy
  obtain ⟨u, rfl⟩ := image_vertex_surjective A (lift id (fun _ => 0)) x
  obtain ⟨v, rfl⟩ := image_vertex_surjective A (lift id (fun _ => 0)) y
  have he : u.val = v.val := congrArg (fun z : Vertex (A.map (id : V → V)) => z.val) hxy
  have huv : u = v := Subtype.ext he
  rw [huv]

/-- Removing nonexactness really loses strict ACTIVE vertex growth. -/
theorem exact_voltage_active_growth_rejected (A : PreAbstractSimplicialComplex V) :
    ExactVoltage (A.map (id : V → V)) (fun _ _ => 0) ∧
      ¬ Nat.card (Vertex (A.map (id : V → V))) <
        Nat.card (Vertex (image A (id : V → V) (fun _ => 0))) := by
  refine ⟨⟨fun _ => 0, by intro u v _; simp⟩, ?_⟩
  have hc := Nat.card_eq_of_bijective _ (zero_height_projection_bijective A)
  omega

/-- Counting the infinite tagged AMBIENT type would erase a nonempty finite image. -/
theorem ambient_cardinality_replacement_rejected :
    Nat.card (Fin 3 ×ₗ ℤ) = 0 ∧
      0 < Nat.card (Vertex (image cycleComplex (id : Fin 3 → Fin 3) (fun _ => 0))) := by
  have : Finite (Vertex (image cycleComplex (id : Fin 3 → Fin 3) (fun _ => 0))) :=
    image_vertices_finite cycleComplex (lift id (fun _ => 0))
  have : Nonempty (Vertex (image cycleComplex (id : Fin 3 → Fin 3) (fun _ => 0))) :=
    ⟨mapVertex (lift id (fun _ => 0)) (le_refl _) cycleBase⟩
  exact ⟨Nat.card_eq_zero_of_infinite, Nat.card_pos⟩

def cycleImageTransport : Transport (K := ℚ) (cycleComplex.map (id : Fin 3 → Fin 3)) :=
  { unit := cycleTransport.unit
    flat := by
      intro u v w huv
      obtain ⟨s, hs, he⟩ := huv
      change s.image id = {u, v, w} at he
      simp only [Finset.image_id] at he
      exact cycleTransport.flat u v w (he ▸ hs) }

/-- Flatness alone does not authorize replacing the inherited transport:
the actual unfilled cycle detects -1 versus 1 after the same height lift. -/
theorem changed_image_transport_rejected :
    let g := lift (id : Fin 3 → Fin 3) (fun _ => (0 : ℤ))
    let p := mapPath g (le_refl (cycleComplex.map g)) cycleLoop
    value (imageTransport cycleComplex id (fun _ => 0) cycleImageTransport) p ≠
      value (PathChains.trivialTransport (K := ℚ) (cycleComplex.map g)) p := by
  dsimp only
  intro he
  have hq := congrArg (fun x : ℚˣ => (x : ℚ)) he
  norm_num [value, mapPath, cycleLoop, imageTransport, pullback, projection,
    lift, heightLift, cycleImageTransport, cycleTransport, PathChains.trivialTransport,
    gaugeTransport] at hq

end D2RelationGap.LiftedImageStep
