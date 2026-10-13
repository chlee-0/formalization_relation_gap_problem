import D2RelationGap.SourceRefinement

/-!
Contextual triangle moves realized in actual mapped source complexes.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. These local constructions do not assemble an arbitrary
target derivation or its final mapped cap, or identify the original character.
-/
noncomputable section
namespace D2RelationGap.SourceMoveSimulation
open OrientedSimplices SimplicialTransport IntegerHeights EdgePaths BasedLoops
open TriangleAttachment SourceRefinement
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

theorem retained_attachment_path {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B)
    (u v w : V) (ht : ({f u,f v,f w} : Finset W) ∈ B) {x y : V} (p : Path A x y) :
    mapPath f (mapped_face A B u v w f hf ht)
      (mapPath id (identity_face_map (inclusion A u v w)) p) = mapPath f hf p := by
  induction p with
  | refl => rfl
  | cons h p ih => simpa only [mapPath,id_eq] using congrArg (Path.cons _) ih

theorem retained_expansion_path {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B)
    (u v : V) (w : W) (ht : ({w,f u,f v} : Finset W) ∈ B)
    {x y : V} (p : Path A x y) :
    mapPath (SourceExpansion.extend f w) (SourceExpansion.extend_face f hf u v w ht)
      (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) p) = mapPath f hf p := by
  have hh : vertices (mapPath (SourceExpansion.extend f w) (SourceExpansion.extend_face f hf u v w ht)
      (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) p)) = vertices (mapPath f hf p) := by
    calc
      _ = (vertices (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) p)).map
          (SourceExpansion.extend f w) := vertices_map _ _ _
      _ = ((vertices p).map SourceExpansion.old).map (SourceExpansion.extend f w) :=
          congrArg (List.map (SourceExpansion.extend f w)) (vertices_map _ _ p)
      _ = (vertices p).map f := by rw [List.map_map]; rfl
      _ = _ := (vertices_map f hf p).symm
  exact vertices_injective hh

theorem steps_map {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {x y : V} (p : Path A x y) :
    steps (mapPath f hf p) = (steps p).map f := by
  induction p with
  | refl => rfl
  | cons h p ih => simpa only [mapPath,steps,List.map_cons] using congrArg (List.cons _) ih

def attachedShortcut (A : PreAbstractSimplicialComplex V) (u v w : V)
    {x y : V} (p : Path A x u) (q : Path A w y) : Path (attachment A u v w) x y :=
  append (mapPath id (identity_face_map (inclusion A u v w)) p)
    (.cons (pair_mem_of_face _ _ (triangle_face A u v w) u w (by simp) (by simp))
      (mapPath id (identity_face_map (inclusion A u v w)) q))

/-- One actual SOURCE triangle move, under any finite prefix and suffix. -/
def attached_shortcut_moves (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    {x y : V} (p : Path A x u) (q : Path A w y) :
    Moves (mapPath id (identity_face_map (inclusion A u v w))
      (append p (.cons huv (.cons hvw q)))) (attachedShortcut A u v w p q) := by
  rw [mapPath_append]
  exact prefixMoves _ (Moves.triangle (triangle_face A u v w) _)

theorem attached_shortcut_projection {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B)
    (u v w : V) (ht : ({f u,f v,f w} : Finset W) ∈ B)
    {x y : V} (p : Path A x u) (q : Path A w y) :
    vertices (mapPath f (mapped_face A B u v w f hf ht) (attachedShortcut A u v w p q)) =
      (steps p).map f ++ f u :: vertices (mapPath f hf q) := by
  rw [attachedShortcut,mapPath_append]
  change vertices (append (mapPath f _ (mapPath id _ p))
    (.cons _ (mapPath f _ (mapPath id _ q)))) = _
  rw [retained_attachment_path f hf u v w ht p,vertices_append,steps_map]
  change _ ++ f u :: vertices (mapPath f _ (mapPath id _ q)) = _
  rw [retained_attachment_path f hf u v w ht q]

def expandedDetour (A : PreAbstractSimplicialComplex V) (u v : V)
    {x y : V} (p : Path A x u) (q : Path A v y) :
    Path (SourceExpansion.expansion A u v) (SourceExpansion.old x) (SourceExpansion.old y) :=
  append (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) p)
    (.cons (pair_mem_of_face _ _ (SourceExpansion.attached_face A u v)
      (SourceExpansion.old u) (SourceExpansion.fresh u) (by simp) (by simp))
      (.cons (pair_mem_of_face _ _ (SourceExpansion.attached_face A u v)
        (SourceExpansion.fresh u) (SourceExpansion.old v) (by simp) (by simp))
        (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) q)))

/-- Insertion creates a genuinely fresh source vertex, even when its target label collapses. -/
def expanded_detour_moves (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) {x y : V} (p : Path A x u) (q : Path A v y) :
    Moves (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) (append p (.cons huv q)))
      (expandedDetour A u v p q) := by
  rw [mapPath_append]
  exact prefixMoves _ (Moves.symm (Moves.triangle (by
    simpa [Finset.insert_comm] using SourceExpansion.attached_face A u v) _))

theorem expanded_detour_projection {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B)
    (u v : V) (w : W) (ht : ({w,f u,f v} : Finset W) ∈ B)
    {x y : V} (p : Path A x u) (q : Path A v y) :
    vertices (mapPath (SourceExpansion.extend f w) (SourceExpansion.extend_face f hf u v w ht)
      (expandedDetour A u v p q)) = (steps p).map f ++ f u :: w :: vertices (mapPath f hf q) := by
  rw [vertices_map,expandedDetour,vertices_append,steps_map]
  simp only [vertices,List.map_append,List.map_cons,vertices_map,List.map_map]
  rfl

theorem included_path_chain {A B : PreAbstractSimplicialComplex V} (hAB : A ≤ B)
    {x y : V} (p : Path A x y) :
    includeEdges hAB (PathChains.chain (PathChains.trivialTransport (K := ℚ) A) p) =
      PathChains.chain (PathChains.trivialTransport (K := ℚ) B) (mapPath id (identity_face_map hAB) p) := by
  induction p with
  | refl => simp [PathChains.chain,mapPath]
  | @cons u v w h p ih =>
    simp only [PathChains.chain,mapPath,id_eq,map_add,ordinary_coeff,one_smul]
    rw [ih]
    exact congrArg (fun z => z + _) (include_oedge hAB u v h)

theorem attached_loop_cycle_span (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    {r : V} (g : Path A r r)
    (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g)) :
    CycleSpan (attachment A u v w) (PathChains.chain (PathChains.trivialTransport (attachment A u v w))
      (mapPath id (identity_face_map (inclusion A u v w)) g)) := by
  rw [← included_path_chain]
  exact cycle_span_preserved A u v w huv hvw _ hs

/-- The generator can be retained while a different contextual path is modified. -/
theorem insertion_retains_generator {K : Type*} [Field K]
    {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (tau : Transport (K := K) B) (f : V → W) (hf : A.map f ≤ B)
    (u v : V) (huv : ({u,v} : Finset V) ∈ A) (w : W)
    (ht : ({w,f u,f v} : Finset W) ∈ B) {r : V} (g : Path A r r)
    (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g)) :
    CycleSpan (SourceExpansion.expansion A u v)
      (PathChains.chain (PathChains.trivialTransport (SourceExpansion.expansion A u v))
        (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) g)) ∧
      value tau (mapPath (SourceExpansion.extend f w) (SourceExpansion.extend_face f hf u v w ht)
        (mapPath SourceExpansion.old (SourceExpansion.old_face A u v) g)) = value tau (mapPath f hf g) :=
  ⟨cycle_span_expanded_loop A u v huv g hs, congrArg (value tau) (retained_expansion_path f hf u v w ht g)⟩

theorem deletion_retains_generator {K : Type*} [Field K]
    {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (tau : Transport (K := K) B) (f : V → W) (hf : A.map f ≤ B)
    (u v w : V) (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A)
    (ht : ({f u,f v,f w} : Finset W) ∈ B) {r : V} (g : Path A r r)
    (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g)) :
    CycleSpan (attachment A u v w)
      (PathChains.chain (PathChains.trivialTransport (attachment A u v w))
        (mapPath id (identity_face_map (inclusion A u v w)) g)) ∧
      value tau (mapPath f (mapped_face A B u v w f hf ht)
        (mapPath id (identity_face_map (inclusion A u v w)) g)) = value tau (mapPath f hf g) :=
  ⟨attached_loop_cycle_span A u v w huv hvw g hs,
    congrArg (value tau) (retained_attachment_path f hf u v w ht g)⟩

/-- A computed source filling permits changing the spanning loop representative. -/
theorem cycle_span_moves (A : PreAbstractSimplicialComplex V) {r : V}
    (g h : Path A r r) (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g))
    (m : Moves g h) : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) h) := by
  have hb := PathChains.filling_boundary (PathChains.trivialTransport (K := ℚ) A) m
  rw [ordinary_coeff] at hb
  intro z hz
  obtain ⟨c,b,hb'⟩ := hs z hz
  refine ⟨c,b + c • PathChains.filling (PathChains.trivialTransport A) m,?_⟩
  rw [map_add,map_smul,hb,smul_sub,hb']
  abel

theorem insertion_source_properties (A : PreAbstractSimplicialComplex V) (u v : V)
    (huv : ({u,v} : Finset V) ∈ A) [Finite (Vertex A)]
    (hd : SimplicialImages.AtMostTwo A) (r : Vertex A)
    (paths : ∀ x : Vertex A, Path A r.val x.val) :
    Finite (Vertex (SourceExpansion.expansion A u v)) ∧
    SimplicialImages.AtMostTwo (SourceExpansion.expansion A u v) ∧
    Nonempty (∀ x : Vertex (SourceExpansion.expansion A u v),
      Path (SourceExpansion.expansion A u v) (SourceExpansion.old r.val) x.val) ∧
    Nat.card (Vertex (SourceExpansion.expansion A u v)) = Nat.card (Vertex A) + 1 :=
  ⟨SourceExpansion.expansion_vertices_finite A u v huv,SourceExpansion.expansion_dimension A u v hd,
    ⟨SourceExpansion.expansionPaths A u v huv r paths⟩,SourceExpansion.expansion_vertex_count A u v huv⟩

theorem deletion_source_properties (A : PreAbstractSimplicialComplex V) (u v w : V)
    (huv : ({u,v} : Finset V) ∈ A) (hvw : ({v,w} : Finset V) ∈ A) [Finite (Vertex A)]
    (hd : SimplicialImages.AtMostTwo A) (r : Vertex A)
    (paths : ∀ x : Vertex A, Path A r.val x.val) :
    Finite (Vertex (attachment A u v w)) ∧ SimplicialImages.AtMostTwo (attachment A u v w) ∧
    Nonempty (∀ x : Vertex (attachment A u v w), Path (attachment A u v w) r.val x.val) ∧
    Nat.card (Vertex (attachment A u v w)) = Nat.card (Vertex A) :=
  ⟨vertices_finite A u v w huv hvw,dimension_at_most_two A u v w hd,
    ⟨rootPaths A u v w huv hvw r paths⟩,active_vertex_count A u v w huv hvw⟩

/-- Wrong fresh labels change the literal projected trace, despite a valid target face. -/
theorem wrong_inserted_vertex_rejected :
    vertices (mapPath (SourceExpansion.extend (id : Fin 3 → Fin 3) 2)
      (SourceExpansion.extend_face (B := (⊤ : PreAbstractSimplicialComplex (Fin 3))) id
        (by rintro s ⟨t,ht,rfl⟩; exact ht.1.image id)
        0 1 2 (Finset.insert_nonempty _ _))
      (expandedDetour cycleComplex 0 1 (.refl 0 cycleBase.property)
        (.refl 1 (by constructor <;> simp)))) ≠ [0,1,1] := by
  rw [expanded_detour_projection (B := (⊤ : PreAbstractSimplicialComplex (Fin 3))) id
    (by rintro s ⟨t,ht,rfl⟩; exact ht.1.image id) 0 1 2 (Finset.insert_nonempty _ _)]
  simp only [steps,vertices,mapPath,id_eq,List.map_nil,List.nil_append]
  decide

/-- The target triangle must exist; edges alone do not authorize the new map. -/
theorem missing_insertion_triangle_rejected :
    ¬ (SourceExpansion.expansion cycleComplex 0 1).map
      (SourceExpansion.extend (id : Fin 3 → Fin 3) 2) ≤ cycleComplex := by
  intro hf
  have hh := image_mem _ hf _ (SourceExpansion.attached_face cycleComplex 0 1)
  have he : ({2,0,1} : Finset (Fin 3)) ∈ cycleComplex := by
    simpa [SourceExpansion.extend,SourceExpansion.old,SourceExpansion.fresh] using hh
  have hc : ({2,0,1} : Finset (Fin 3)).card ≤ 2 := he.2
  norm_num at hc

/-- A collapsed target backtrack can leave distinct source endpoints on the shortcut. -/
theorem collapsed_backtrack_keeps_source_edge :
    vertices (attachedShortcut cycleComplex 0 1 2 (.refl 0 cycleBase.property)
      (.refl 2 (by constructor <;> simp))) = [0,2] ∧
    [0,2].map (fun _ : Fin 3 => (0 : Fin 1)) = [0,0] ∧ (0 : Fin 3) ≠ 2 := by
  constructor
  · rfl
  constructor <;> decide

end D2RelationGap.SourceMoveSimulation
