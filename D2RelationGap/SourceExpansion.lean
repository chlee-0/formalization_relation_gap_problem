import D2RelationGap.SixVertexSource

/-!
Actual elementary simplicial source expansions and ordinary rational chain homotopies.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. A general refined Moore map and geometric adequacy remain open.
-/
noncomputable section
namespace D2RelationGap.SourceExpansion
open OrientedSimplices SimplicialTransport PathChains IntegerHeights
variable {U V W : Type*} [LinearOrder U] [LinearOrder V] [LinearOrder W]

abbrev oedge (A : PreAbstractSimplicialComplex V) (u v : V)
    (h : ({u,v} : Finset V) ∈ A) := edge (trivialTransport (K := ℚ) A) u v h
abbrev otriangle (A : PreAbstractSimplicialComplex V) (u v w : V)
    (h : ({u,v,w} : Finset V) ∈ A) := triangle (trivialTransport (K := ℚ) A) u v w h
abbrev emap {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) := edgeMap (trivialTransport (K := ℚ) B) f hf
abbrev tmap {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) := triangleMap (trivialTransport (K := ℚ) B) f hf

theorem ordinary_map_one {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) :
    (ordinaryOne B).comp (emap f hf) = (vertexMap (K := ℚ) f hf).comp (ordinaryOne A) := by
  have h := map_boundary_one (trivialTransport (K := ℚ) B) f hf
  have hp : coeff (pullback (trivialTransport (K := ℚ) B) f hf) =
      (fun _ _ => (1 : ℚ)) := by
    funext x y
    simp [coeff, pullback, trivialTransport, gaugeTransport]
  rw [ordinary_coeff, hp] at h
  exact h

theorem ordinary_map_two {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) :
    (ordinaryTwo B).comp (tmap f hf) = (emap f hf).comp (ordinaryTwo A) := by
  have h := map_boundary_two (trivialTransport (K := ℚ) B) f hf
  have hp : coeff (pullback (trivialTransport (K := ℚ) B) f hf) =
      (fun _ _ => (1 : ℚ)) := by
    funext x y
    simp [coeff, pullback, trivialTransport, gaugeTransport]
  rw [ordinary_coeff, hp] at h
  exact h

theorem emap_edge {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) (u v : U) (h : ({u,v} : Finset U) ∈ A) :
    emap f hf (oedge A u v h) = oedge B (f u) (f v) (by simpa using image_mem f hf _ h) := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · simp [emap, oedge, edge, huv, edgeMap]
  · simp [oedge, edge]
  · have hh := edge_reverse (trivialTransport (K := ℚ) B) (f u) (f v)
      (by simpa using image_mem f hf _ h)
    rw [ordinary_coeff, one_smul] at hh
    simpa [emap, oedge, edge, hvu, not_lt_of_gt hvu, ordinary_coeff, edgeMap]
      using (neg_eq_iff_eq_neg.mpr hh)

theorem emap_single {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) (e : Edge A) (c : ℚ) :
    emap f hf (Finsupp.single e c) = c • oedge B (f e.src) (f e.dst)
      (by simpa using image_mem f hf _ e.face) := by simp [emap, edgeMap, oedge]

theorem ordinary_triangle_boundary (A : PreAbstractSimplicialComplex V) (u v w : V)
    (h : ({u,v,w} : Finset V) ∈ A) :
    ordinaryTwo A (otriangle A u v w h) =
      oedge A v w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) -
      oedge A u w (pair_mem_of_face A _ h _ _ (by simp) (by simp)) +
      oedge A u v (pair_mem_of_face A _ h _ _ (by simp) (by simp)) := by
  have hh := triangle_boundary (trivialTransport (K := ℚ) A) u v w h
  rw [ordinary_coeff, one_smul] at hh
  exact hh

theorem emap_comp {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    {C : PreAbstractSimplicialComplex W} (f : U → V) (hf : A.map f ≤ B)
    (g : V → W) (hg : B.map g ≤ C) (hgf : A.map (g ∘ f) ≤ C) :
    (emap g hg).comp (emap f hf) = emap (g ∘ f) hgf := by
  apply Finsupp.lhom_ext
  intro e c
  simp only [LinearMap.comp_apply, emap_single, map_smul, emap_edge, Function.comp_apply]

/-- Only edge contiguity is needed in degrees zero and one. The actual face
condition includes every orientation and every collapsed edge. -/
def EdgeContiguous (A : PreAbstractSimplicialComplex V) (k : V → V) : Prop :=
  ∀ u v, ({u,v} : Finset V) ∈ A → ({u,v,k u,k v} : Finset V) ∈ A

def prismZero (A : PreAbstractSimplicialComplex V) (k : V → V)
    (hc : EdgeContiguous A k) : (Vertex A →₀ ℚ) →ₗ[ℚ] Edge A →₀ ℚ :=
  Finsupp.linearCombination ℚ fun v => oedge A v.val (k v.val) (by
    exact pair_mem_of_face A _ (hc v.val v.val (by simpa using v.property)) _ _ (by simp) (by simp))

def prismOne (A : PreAbstractSimplicialComplex V) (k : V → V)
    (hc : EdgeContiguous A k) : (Edge A →₀ ℚ) →ₗ[ℚ] Triangle A →₀ ℚ :=
  Finsupp.linearCombination ℚ fun e =>
    otriangle A e.src (k e.src) (k e.dst) (by
      exact (A.isRelLowerSet_faces (hc e.src e.dst e.face)).2 (by simp) (by simp)) -
    otriangle A e.src e.dst (k e.dst) (by
      exact (A.isRelLowerSet_faces (hc e.src e.dst e.face)).2 (by simp) (by simp))

theorem prism_identity (A : PreAbstractSimplicialComplex V) (k : V → V)
    (hk : A.map k ≤ A) (hc : EdgeContiguous A k) :
    (ordinaryTwo A).comp (prismOne A k hc) + (prismZero A k hc).comp (ordinaryOne A) =
      emap k hk - LinearMap.id := by
  apply Finsupp.lhom_ext
  intro e c
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, prismOne, Finsupp.linearCombination_single, map_smul, map_sub,
    ordinary_triangle_boundary]
  have he : oedge A e.src e.dst e.face = Finsupp.single e 1 := by
    simp [oedge, edge, e.ordered]
  simp only [prismZero, ordinaryOne, boundaryOne, VoltageChains.baseOne,
    Finsupp.linearCombination_single, incidence, map_smul, map_sub, one_smul,
    emap_single, smul_sub, smul_add, he]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  abel

/-- Degree-one exactness transfers through actual face maps and a proved prism.
The homotopy is computed above; exactness on the expanded complex is not assumed. -/
theorem exactness_of_retraction {A : PreAbstractSimplicialComplex U}
    {B : PreAbstractSimplicialComplex V} (r : V → U) (hr : B.map r ≤ A)
    (i : U → V) (hi : A.map i ≤ B) (hk : B.map (i ∘ r) ≤ B)
    (hc : EdgeContiguous B (i ∘ r))
    (hex : LinearMap.range (ordinaryTwo A) = LinearMap.ker (ordinaryOne A)) :
    LinearMap.range (ordinaryTwo B) = LinearMap.ker (ordinaryOne B) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w, rfl⟩ := hz
    change ordinaryOne B (ordinaryTwo B w) = 0
    have hb := unit_boundary_chain (trivialTransport (K := ℚ) B)
    rw [ordinary_coeff] at hb
    exact LinearMap.congr_fun hb w
  · intro z hz
    have hz0 : ordinaryOne B z = 0 := hz
    have hrz : ordinaryOne A (emap r hr z) = 0 := by
      have h := LinearMap.congr_fun (ordinary_map_one r hr) z
      simpa [hz0] using h
    have hzA : emap r hr z ∈ LinearMap.range (ordinaryTwo A) := by rw [hex]; exact hrz
    obtain ⟨w, hw⟩ := hzA
    refine ⟨tmap i hi w - prismOne B (i ∘ r) hc z, ?_⟩
    have h2 := LinearMap.congr_fun (ordinary_map_two i hi) w
    have hp := LinearMap.congr_fun (prism_identity B (i ∘ r) hk hc) z
    have hcomp := LinearMap.congr_fun (emap_comp r hr i hi hk) z
    simp only [LinearMap.comp_apply] at h2 hcomp
    rw [hw, hcomp] at h2
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.id_apply, hz0, map_zero, add_zero] at hp
    rw [map_sub, h2, hp]
    abel

/-- A fresh vertex is attached by one triangle along the source edge. This is
an elementary expansion, not a claim of geometric subdivision equivalence. -/
abbrev Ambient (V : Type*) := Bool ×ₗ V

def old (v : V) : Ambient V := toLex (true, v)
def fresh (u : V) : Ambient V := toLex (false, u)
def retract (p : Ambient V) : V := (ofLex p).2

def expansion (A : PreAbstractSimplicialComplex V) (u v : V) :
    PreAbstractSimplicialComplex (Ambient V) where
  faces := {s | s ∈ A.map old ∨ s.Nonempty ∧ s ⊆ {fresh u, old u, old v}}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rcases hs with hs | hs
      · exact (A.map old).isRelLowerSet_faces hs |>.1
      · exact hs.1
    · intro t hts ht
      rcases hs with hs | hs
      · exact Or.inl (((A.map old).isRelLowerSet_faces hs).2 hts ht)
      · exact Or.inr ⟨ht, hts.trans hs.2⟩

theorem old_face (A : PreAbstractSimplicialComplex V) (u v : V) :
    A.map old ≤ expansion A u v := fun _ hs => Or.inl hs

theorem attached_face (A : PreAbstractSimplicialComplex V) (u v : V) :
    ({fresh u, old u, old v} : Finset (Ambient V)) ∈ expansion A u v :=
  Or.inr ⟨Finset.insert_nonempty _ _, Finset.Subset.refl _⟩

theorem retract_face (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) : (expansion A u v).map retract ≤ A := by
  rintro s ⟨t, ht, rfl⟩
  rcases ht with ⟨q, hq, rfl⟩ | ⟨ht, hts⟩
  · simpa [Finset.image_image, Function.comp_def, retract, old] using hq
  · apply (A.isRelLowerSet_faces huv).2
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      have hh := hts hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> simp [retract, old, fresh]
    · exact ht.image retract

omit [LinearOrder V] in
theorem retract_old (v : V) : retract (old v) = v := rfl

theorem expansion_contiguous (A : PreAbstractSimplicialComplex V) (u v : V) :
    EdgeContiguous (expansion A u v) (old ∘ retract) := by
  intro p q hpq
  rcases hpq with ⟨s, hs, he⟩ | ⟨hne, hsub⟩
  · change s.image old = {p,q} at he
    have hp : ∃ x, old x = p := by
      have h : p ∈ s.image old := by rw [he]; simp
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
      exact ⟨x, hx⟩
    have hq : ∃ y, old y = q := by
      have h : q ∈ s.image old := by rw [he]; simp
      obtain ⟨y, _, hy⟩ := Finset.mem_image.mp h
      exact ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    apply Or.inl
    simpa [Function.comp_def, retract_old] using (show ({old x, old y} : Finset (Ambient V)) ∈ A.map old from ⟨s, hs, he⟩)
  · apply Or.inr
    refine ⟨by simp, ?_⟩
    have hp := hsub (by simp : p ∈ ({p,q} : Finset (Ambient V)))
    have hq := hsub (by simp : q ∈ ({p,q} : Finset (Ambient V)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton, Function.comp_apply] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl
    · exact hp
    · exact hq
    · rcases hp with rfl | rfl | rfl <;> simp [retract, old, fresh]
    · rcases hq with rfl | rfl | rfl <;> simp [retract, old, fresh]

theorem expansion_map_retraction (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) : (expansion A u v).map (old ∘ retract) ≤ expansion A u v := by
  rintro s ⟨t, ht, rfl⟩
  exact old_face A u v ⟨t.image retract, image_mem retract (retract_face A u v huv) t ht,
    by simp [Finset.image_image]⟩

theorem expansion_exactness (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A)
    (hex : LinearMap.range (ordinaryTwo A) = LinearMap.ker (ordinaryOne A)) :
    LinearMap.range (ordinaryTwo (expansion A u v)) =
      LinearMap.ker (ordinaryOne (expansion A u v)) :=
  exactness_of_retraction retract (retract_face A u v huv) old (old_face A u v)
    (expansion_map_retraction A u v huv) (expansion_contiguous A u v) hex


def expansionVertex (A : PreAbstractSimplicialComplex V) (u v : V) :
    Vertex A ⊕ Unit → Vertex (expansion A u v)
  | .inl x => mapVertex old (old_face A u v) x
  | .inr _ => ⟨fresh u, vertex_mem_of_face _ _ (attached_face A u v) _ (by simp)⟩

theorem expansion_vertex_surjective (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) : Function.Surjective (expansionVertex A u v) := by
  rintro ⟨p,hp⟩
  rcases hp with hp | ⟨_,hp⟩
  · obtain ⟨x,hx⟩ := LiftedImageStep.image_vertex_surjective A old ⟨p,hp⟩
    exact ⟨.inl x, Subtype.ext (congrArg (fun p : Vertex (A.map old) => p.val) hx)⟩
  · have hh := hp (by simp : p ∈ ({p} : Finset (Ambient V)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl
    · exact ⟨.inr (), rfl⟩
    · exact ⟨.inl ⟨u, vertex_mem_of_face A _ huv _ (by simp)⟩, rfl⟩
    · exact ⟨.inl ⟨v, vertex_mem_of_face A _ huv _ (by simp)⟩, rfl⟩

theorem expansion_vertex_injective (A : PreAbstractSimplicialComplex V) (u v : V) :
    Function.Injective (expansionVertex A u v) := by
  intro x y he
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact congrArg (fun p => (ofLex p.val).2) he
    | inr y =>
      have hh := congrArg (fun p => (ofLex p.val).1) he
      simp [expansionVertex, mapVertex, old, fresh] at hh
  | inr x =>
    cases y with
    | inl y =>
      have hh := congrArg (fun p => (ofLex p.val).1) he
      simp [expansionVertex, mapVertex, old, fresh] at hh
    | inr y => rfl

theorem expansion_vertices_finite (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) [Finite (Vertex A)] :
    Finite (Vertex (expansion A u v)) :=
  Finite.of_surjective _ (expansion_vertex_surjective A u v huv)

theorem expansion_vertex_count (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) [Finite (Vertex A)] :
    Nat.card (Vertex (expansion A u v)) = Nat.card (Vertex A) + 1 := by
  have he := Nat.card_congr (Equiv.ofBijective (expansionVertex A u v)
    ⟨expansion_vertex_injective A u v, expansion_vertex_surjective A u v huv⟩)
  simpa using he.symm

theorem expansion_dimension (A : PreAbstractSimplicialComplex V) (u v : V)
    (hA : ∀ s, s ∈ A → s.card ≤ 3) :
    ∀ s, s ∈ expansion A u v → s.card ≤ 3 := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩ | ⟨_,ht⟩
  · exact Finset.card_image_le.trans (hA t ht)
  · exact (Finset.card_le_card ht).trans Finset.card_le_three

open EdgePaths BasedLoops

def expansionPaths (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) (r : Vertex A)
    (paths : ∀ x : Vertex A, Path A r.val x.val)
    (p : Vertex (expansion A u v)) : Path (expansion A u v) (old r.val) p.val :=
  append (mapPath old (old_face A u v) (paths (mapVertex retract (retract_face A u v huv) p)))
    (single (pair_mem_of_face _ _ (expansion_contiguous A u v p.val p.val
      (by simpa using p.property)) _ _ (by simp [mapVertex]) (by simp)))

/-- A target triangle supplies the map on the fresh vertex. Unused ambient
vertices also map to w; only actual source faces matter. -/
def extend (f : V → W) (w : W) (p : Ambient V) : W :=
  if (ofLex p).1 then f (ofLex p).2 else w

omit [LinearOrder V] [LinearOrder W] in
theorem extend_old (f : V → W) (w : W) (v : V) : extend f w (old v) = f v := rfl

theorem extend_face {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (u v : V) (w : W)
    (ht : ({w,f u,f v} : Finset W) ∈ B) : (expansion A u v).map (extend f w) ≤ B := by
  rintro s ⟨t, ht', rfl⟩
  rcases ht' with ⟨q,hq,rfl⟩ | ⟨hne,hsub⟩
  · have he : extend f w ∘ old = f := funext (extend_old f w)
    change (q.image old).image (extend f w) ∈ B
    rw [Finset.image_image, he]
    exact image_mem f hf q hq
  · apply (B.isRelLowerSet_faces ht).2
    · intro z hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      have hh := hsub hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> simp [extend, old, fresh]
    · exact hne.image _

/-- The attached triangle supplies a literal finite move replacing the old edge
by its two-edge detour. This does not yet assemble an arbitrary null witness. -/
def edge_detour_moves (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) :
    Moves (single (by simpa using image_mem old (old_face A u v) _ huv))
      (Path.cons (pair_mem_of_face _ _ (attached_face A u v) (old u) (fresh u) (by simp) (by simp))
        (single (pair_mem_of_face _ _ (attached_face A u v) (fresh u) (old v) (by simp) (by simp)))) :=
  Moves.symm (Moves.triangle (by
    simpa [Finset.insert_comm] using attached_face A u v)
    (Path.refl (old v) (vertex_mem_of_face _ _ (attached_face A u v) _ (by simp))))

variable {K : Type*} [Field K]

theorem extension_pullback {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (tau : Transport (K := K) B)
    (f : V → W) (hf : A.map f ≤ B) (u v : V) (w : W)
    (ht : ({w,f u,f v} : Finset W) ∈ B) :
    pullback (pullback tau (extend f w) (extend_face f hf u v w ht)) old (old_face A u v) =
      pullback tau f hf := rfl

theorem extension_path_value {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (tau : Transport (K := K) B)
    (f : V → W) (hf : A.map f ≤ B) (u v : V) (w : W)
    (ht : ({w,f u,f v} : Finset W) ∈ B) {x y : V} (p : Path A x y) :
    value (pullback tau (extend f w) (extend_face f hf u v w ht))
      (mapPath old (old_face A u v) p) = value (pullback tau f hf) p := by
  rw [value_mapPath]
  exact congrArg (fun t : Transport (K := K) A => value t p)
    (extension_pullback tau f hf u v w ht)

theorem six_source_expansion_exactness (u v : Fin 6) :
    LinearMap.range (ordinaryTwo (expansion SixVertexSource.source u v)) =
      LinearMap.ker (ordinaryOne (expansion SixVertexSource.source u v)) :=
  expansion_exactness _ u v (SixVertexSource.pair_face u v) SixVertexSource.ordinary_chain_exactness



theorem six_source_expansion_generator_value (u v : Fin 6) :
    value (pullback SixVertexSource.signTransport retract
      (retract_face SixVertexSource.source u v (SixVertexSource.pair_face u v)))
      (mapPath old (old_face SixVertexSource.source u v) SixVertexSource.generatorPath) = -1 := by
  rw [value_mapPath]
  exact SixVertexSource.generator_value


theorem six_source_expansion_vertex_count (u v : Fin 6) :
    Nat.card (Vertex (expansion SixVertexSource.source u v)) = 7 := by
  rw [expansion_vertex_count _ u v (SixVertexSource.pair_face u v), SixVertexSource.active_vertex_count]


theorem six_source_expansion_dimension (u v : Fin 6) :
    SimplicialImages.AtMostTwo (expansion SixVertexSource.source u v) :=
  expansion_dimension _ u v SixVertexSource.dimension_at_most_two

theorem omitted_fresh_vertex_count_rejected (u v : Fin 6) :
    Nat.card (Vertex (expansion SixVertexSource.source u v)) ≠
      Nat.card (Vertex SixVertexSource.source) := by
  rw [six_source_expansion_vertex_count, SixVertexSource.active_vertex_count]
  decide

/-- The fresh vertex cannot fill the unfilled target cycle without a triangle. -/
theorem missing_target_triangle_rejected :
    ¬ (expansion (⊤ : PreAbstractSimplicialComplex (Fin 2)) 0 1).map
      (extend (fun x : Fin 2 => if x = 0 then (0 : Fin 3) else 1) 2) ≤ cycleComplex := by
  intro hf
  have ht := image_mem _ hf _ (attached_face (⊤ : PreAbstractSimplicialComplex (Fin 2)) 0 1)
  norm_num [Finset.image_insert, Finset.image_singleton, extend, old, fresh] at ht
  change ({2,0,1} : Finset (Fin 3)).Nonempty ∧ ({2,0,1} : Finset (Fin 3)).card ≤ 2 at ht
  exact (by decide : ¬ (({2,0,1} : Finset (Fin 3)).Nonempty ∧
    ({2,0,1} : Finset (Fin 3)).card ≤ 2)) ht

/-- An edge prism alone has the wrong boundary sign on a triangle. -/
theorem reversed_prism_boundary_rejected :
    let A : PreAbstractSimplicialComplex (Fin 3) := ⊤
    let ht : ({0,1,2} : Finset (Fin 3)) ∈ A := Finset.insert_nonempty _ _
    ordinaryTwo A (-otriangle A 0 1 2 ht) ≠
      oedge A 1 2 (Finset.insert_nonempty _ _) -
      oedge A 0 2 (Finset.insert_nonempty _ _) + oedge A 0 1 (Finset.insert_nonempty _ _) := by
  dsimp only
  intro he
  let e : Edge (⊤ : PreAbstractSimplicialComplex (Fin 3)) :=
    ⟨0,1,by decide,Finset.insert_nonempty _ _⟩
  have hh := congrArg (fun z : Edge (⊤ : PreAbstractSimplicialComplex (Fin 3)) →₀ ℚ => z e) he
  norm_num [map_neg, ordinary_triangle_boundary, oedge, edge, ordinary_coeff,
    e, Finsupp.single_apply, Edge.ext_iff] at hh

end D2RelationGap.SourceExpansion
