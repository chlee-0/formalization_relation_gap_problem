import D2RelationGap.TriangleTraceUpdate

/-!
Constructed reverse target moves with actual fresh source embeddings.
Credit: OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
Joint schedule/source history and original-character/geometric adequacy remain open.
-/
noncomputable section
namespace D2RelationGap.InsertionTraceUpdate
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops SourceRefinement
open SourceMoveSimulation TriangleAttachment StutterTrace TraceAlignment TriangleTraceUpdate
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- The source is a literal one-fresh-vertex expansion at a computed actual edge. -/
structure Insertion {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {u v : V} (p : Path A u v) (target : Path B (f u) (f v)) (label : W) where
  src : V
  dst : V
  face : ({src,dst} : Finset V) ∈ A
  face_map : (SourceExpansion.expansion A src dst).map (SourceExpansion.extend f label) ≤ B
  upper : Path (SourceExpansion.expansion A src dst) (SourceExpansion.old u) (SourceExpansion.old v)
  moves : Moves (mapPath SourceExpansion.old (SourceExpansion.old_face A src dst) p) upper
  realizes : Realizes (SourceExpansion.extend f label) face_map upper target

theorem detour_trace {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (a c : V) (b : W)
    (ht : ({b,f a,f c} : Finset W) ∈ B) {u v : V} (pre : Path A u a) (post : Path A c v)
    (hl : ∀ z ∈ vertices pre, f z = f a) :
    vertices (imageTrace (SourceExpansion.extend f b) (SourceExpansion.extend_face f hf a c b ht)
      (expandedDetour A a c pre post)) =
      if f a = b then
        (if b = f c then vertices (imageTrace f hf post) else b :: vertices (imageTrace f hf post))
      else f a :: (if b = f c then vertices (imageTrace f hf post) else b :: vertices (imageTrace f hf post)) := by
  let ff := SourceExpansion.extend f b
  let hh := SourceExpansion.extend_face f hf a c b ht
  let hi := SourceExpansion.old_face A a c
  have hpre : ∀ z ∈ vertices (mapPath SourceExpansion.old hi pre), ff z = ff (SourceExpansion.old a) := by
    rw [vertices_map]
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact hl x hx
  rw [expandedDetour,constant_before_trace ff hh _ _ hpre]
  have h1 : ({SourceExpansion.old a,SourceExpansion.fresh a} : Finset (SourceExpansion.Ambient V)) ∈
      SourceExpansion.expansion A a c :=
    pair_mem_of_face _ _ (SourceExpansion.attached_face A a c) _ _ (by simp) (by simp)
  have h2 : ({SourceExpansion.fresh a,SourceExpansion.old c} : Finset (SourceExpansion.Ambient V)) ∈
      SourceExpansion.expansion A a c :=
    pair_mem_of_face _ _ (SourceExpansion.attached_face A a c) _ _ (by simp) (by simp)
  have hp : imageTrace ff hh (mapPath SourceExpansion.old hi post) = imageTrace f hf post :=
    congrArg StutterTrace.normalize (retained_expansion_path f hf a c b ht post)
  have hm := imageTrace_cons_vertices ff hh h1 (.cons h2 (mapPath SourceExpansion.old hi post))
  have hn := imageTrace_cons_vertices ff hh h2 (mapPath SourceExpansion.old hi post)
  exact hm.trans (by rw [hn,hp]; rfl)

theorem normalize_two_vertices {B : PreAbstractSimplicialComplex W} {a b c v : W}
    (h1 : ({a,b} : Finset W) ∈ B) (h2 : ({b,c} : Finset W) ∈ B) (post : Path B c v) :
    vertices (StutterTrace.normalize (.cons h1 (.cons h2 post))) =
      if a = b then
        (if b = c then vertices (StutterTrace.normalize post) else b :: vertices (StutterTrace.normalize post))
      else a :: (if b = c then vertices (StutterTrace.normalize post) else b :: vertices (StutterTrace.normalize post)) := by
  rw [normalize_cons_vertices,normalize_cons_vertices]

/-- SOURCE backtrack insertion at a literal endpoint. No source endpoints are merged. -/
def leaf_moves (A : PreAbstractSimplicialComplex V) {u v : V} (p : Path A u v) :
    Moves (mapPath SourceExpansion.old (SourceExpansion.old_face A u u) p)
      (expandedDetour A u u (.refl u (startActive p)) p) := by
  have huu : ({u,u} : Finset V) ∈ A := by simpa using startActive p
  have m1 := mapMoves SourceExpansion.old (SourceExpansion.old_face A u u)
    (Moves.symm (Moves.stutter (startActive p) p))
  have m2 := expanded_detour_moves A u u huu (.refl u (startActive p)) p
  exact .trans m1 m2

/-- Extract an actual noncollapsed source edge and expand it with the new target label. -/
def insertEdge {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (b c : W)
    (ht : ({f u,b,c} : Finset W) ∈ B) (post : Path B c (f v))
    (he : vertices (imageTrace f hf p) = f u :: vertices (StutterTrace.normalize post)) :
    Insertion f p (.cons (pair_mem_of_face _ _ ht (f u) b (by simp) (by simp))
      (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post)) b := by
  have he' : vertices (imageTrace f hf p) = f u :: c :: (vertices (StutterTrace.normalize post)).tail :=
    he.trans (congrArg (List.cons (f u)) (vertices_eq_start_tail (StutterTrace.normalize post)))
  let t := firstSplit f hf p c (vertices (StutterTrace.normalize post)).tail he'
  have htri : ({b,f t.src,f t.dst} : Finset W) ∈ B := by
    rw [t.src_label,t.dst_label]
    simpa only [Finset.insert_comm] using ht
  refine ⟨t.src,t.dst,t.face,SourceExpansion.extend_face f hf t.src t.dst b htri,
    expandedDetour A t.src t.dst t.before t.suffix,?_,?_⟩
  · have m := expanded_detour_moves A t.src t.dst t.face t.before t.suffix
    have hp := congrArg (mapPath SourceExpansion.old (SourceExpansion.old_face A t.src t.dst)) t.decomposition
    exact hp.symm ▸ m
  · apply vertices_injective
    have hl : ∀ z ∈ vertices t.before, f z = f t.src :=
      fun z hz => (t.before_labels z hz).trans t.src_label.symm
    have hs : vertices (imageTrace f hf t.suffix) = vertices (StutterTrace.normalize post) :=
      t.suffix_trace.trans (vertices_eq_start_tail (StutterTrace.normalize post)).symm
    change vertices (imageTrace _ _ _) = vertices (StutterTrace.normalize (.cons _ (.cons _ post)))
    rw [detour_trace f hf t.src t.dst b htri _ _ hl,hs,t.src_label,t.dst_label]
    exact (normalize_two_vertices (pair_mem_of_face _ _ ht (f u) b (by simp) (by simp))
      (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post).symm

/-- Every reverse triangle move at the head, including all collapsed target labels. -/
def insertHead {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (b c : W)
    (ht : ({f u,b,c} : Finset W) ∈ B) (post : Path B c (f v))
    (h : Realizes f hf p (.cons (pair_mem_of_face _ _ ht (f u) c (by simp) (by simp)) post)) :
    Insertion f p (.cons (pair_mem_of_face _ _ ht (f u) b (by simp) (by simp))
      (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post)) b := by
  by_cases hac : f u = c
  · subst c
    have htri : ({b,f u,f u} : Finset W) ∈ B := by simpa only [Finset.insert_comm] using ht
    have hl : ∀ z ∈ vertices (.refl u (startActive p) : Path A u u), f z = f u := by
      intro z hz
      have hz' : z = u := by simpa [vertices] using hz
      exact congrArg f hz'
    refine ⟨u,u,by simpa using startActive p,SourceExpansion.extend_face f hf u u b htri,
      expandedDetour A u u (.refl u (startActive p)) p,leaf_moves A p,?_⟩
    apply vertices_injective
    have hp : imageTrace f hf p = StutterTrace.normalize post := h.trans (by simp [StutterTrace.normalize])
    change vertices (imageTrace _ _ _) = vertices (StutterTrace.normalize (.cons _ (.cons _ post)))
    rw [detour_trace f hf u u b htri _ _ hl,hp]
    exact (normalize_two_vertices (pair_mem_of_face _ _ ht (f u) b (by simp) (by simp))
      (pair_mem_of_face _ _ ht b (f u) (by simp) (by simp)) post).symm
  · apply insertEdge f hf p b c ht post
    have hp := congrArg vertices h
    rw [normalize_cons_vertices,ite_eq_right hac] at hp
    exact hp

/-- Wrap the computed fresh insertion under an actual matching SOURCE prefix. -/
def inContext {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u x v : V} (pre : Path A u x) (p : Path A x v)
    (tpre : Path B (f u) (f x)) (q : Path B (f x) (f v)) (b : W)
    (hpre : Realizes f hf pre tpre) (s : Insertion f p q b) :
    Insertion f (append pre p) (append tpre q) b := by
  have htri : ({b,f s.src,f s.dst} : Finset W) ∈ B := by
    have hh := image_mem (SourceExpansion.extend f b) s.face_map _ (SourceExpansion.attached_face A s.src s.dst)
    simp only [Finset.image_insert,Finset.image_singleton] at hh
    exact hh
  refine ⟨s.src,s.dst,s.face,s.face_map,
    append (mapPath SourceExpansion.old (SourceExpansion.old_face A s.src s.dst) pre) s.upper,?_,?_⟩
  · rw [mapPath_append]; exact prefixMoves _ s.moves
  · apply realizes_append
    · have he := retained_expansion_path f hf s.src s.dst b htri pre
      exact (congrArg StutterTrace.normalize he).trans hpre
    · exact s.realizes


/-- Compute an actual source cut from Realizes, then insert under arbitrary TARGET context. -/
def insertContext {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (a b c : W)
    (ht : ({a,b,c} : Finset W) ∈ B) (pre : Path B (f u) a) (post : Path B c (f v))
    (h : Realizes f hf p (append pre (.cons (pair_mem_of_face _ _ ht a c (by simp) (by simp)) post))) :
    Insertion f p (append pre (.cons (pair_mem_of_face _ _ ht a b (by simp) (by simp))
      (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post))) b := by
  let oldTail := Path.cons (pair_mem_of_face _ _ ht a c (by simp) (by simp)) post
  let t := cutAtTargetContext f hf p a pre oldTail h
  have htri : ({f t.node,b,c} : Finset W) ∈ B := by rw [t.node_label]; exact ht
  have ha := cut_after_realizes f hf p a pre oldTail h
  have hc := castStart_cons t.node_label.symm (pair_mem_of_face _ _ ht a c (by simp) (by simp))
    (pair_mem_of_face _ _ htri (f t.node) c (by simp) (by simp)) post
  have ha' : Realizes f hf t.after (.cons (pair_mem_of_face _ _ htri (f t.node) c (by simp) (by simp)) post) :=
    ha.trans (congrArg StutterTrace.normalize hc)
  let inner := insertHead f hf t.after b c htri post ha'
  let wrapped := inContext f hf t.before t.after (castEnd t.node_label.symm pre)
    (.cons (pair_mem_of_face _ _ htri (f t.node) b (by simp) (by simp))
      (.cons (pair_mem_of_face _ _ htri b c (by simp) (by simp)) post)) b
    (cut_before_realizes f hf p a pre oldTail h) inner
  have hsource := congrArg (mapPath SourceExpansion.old (SourceExpansion.old_face A wrapped.src wrapped.dst)) t.decomposition
  have htarget : append (castEnd t.node_label.symm pre)
      (.cons (pair_mem_of_face _ _ htri (f t.node) b (by simp) (by simp))
        (.cons (pair_mem_of_face _ _ htri b c (by simp) (by simp)) post)) =
      append pre (.cons (pair_mem_of_face _ _ ht a b (by simp) (by simp))
        (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post)) :=
    (congrArg (append (castEnd t.node_label.symm pre))
      (castStart_cons t.node_label.symm (pair_mem_of_face _ _ ht a b (by simp) (by simp))
        (pair_mem_of_face _ _ htri (f t.node) b (by simp) (by simp))
        (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post)).symm).trans
      (append_cast t.node_label.symm pre (.cons (pair_mem_of_face _ _ ht a b (by simp) (by simp))
        (.cons (pair_mem_of_face _ _ ht b c (by simp) (by simp)) post)))
  refine ⟨wrapped.src,wrapped.dst,wrapped.face,wrapped.face_map,wrapped.upper,?_,?_⟩
  · exact hsource.symm ▸ wrapped.moves
  · exact wrapped.realizes.trans (congrArg StutterTrace.normalize htarget)

/-- Reverse backtracks use a literal source leaf at the computed cut. -/
def insertBacktrack {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (a b : W)
    (hab : ({a,b} : Finset W) ∈ B) (pre : Path B (f u) a) (post : Path B a (f v))
    (h : Realizes f hf p (append pre post)) :
    Insertion f p (append pre (.cons hab (.cons (by simpa only [Finset.pair_comm] using hab) post))) b := by
  have he : ({a,b,a} : Finset W) = {a,b} := by ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  have ht : ({a,b,a} : Finset W) ∈ B := by rw [he]; exact hab
  have htrace : StutterTrace.normalize (append pre (.cons (pair_mem_of_face _ _ ht a a (by simp) (by simp)) post)) =
      StutterTrace.normalize (append pre post) := by
    apply normalize_prefix_congr
    simp [StutterTrace.normalize]
  exact insertContext f hf p a b a ht pre post (h.trans htrace.symm)

/-- Stutter insertion uses the same fresh-source interface, with constant new labels. -/
def insertStutter {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (a : W)
    (ha : ({a} : Finset W) ∈ B) (pre : Path B (f u) a) (post : Path B a (f v))
    (h : Realizes f hf p (append pre post)) :
    Insertion f p (append pre (.cons (by simpa using ha) post)) a := by
  have hab : ({a,a} : Finset W) ∈ B := by simpa using ha
  let s := insertBacktrack f hf p a a hab pre post h
  have htrace : StutterTrace.normalize (append pre (.cons hab (.cons (by simpa using ha) post))) =
      StutterTrace.normalize (append pre (.cons (by simpa using ha) post)) := by
    apply normalize_prefix_congr
    simp [StutterTrace.normalize]
  exact ⟨s.src,s.dst,s.face,s.face_map,s.upper,s.moves,s.realizes.trans htrace⟩

/-- The actual existing SOURCE square-to-upper derivation is mapped, not inferred from target nullity. -/
def squareStage {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {r : V} (g p : Path A r r) (q : Path B (f r) (f r)) (b : W)
    (s : Insertion f p q b) (m : Moves (append g g) p) :
    Moves (append (mapPath SourceExpansion.old (SourceExpansion.old_face A s.src s.dst) g)
      (mapPath SourceExpansion.old (SourceExpansion.old_face A s.src s.dst) g)) s.upper := by
  have hm := mapMoves SourceExpansion.old (SourceExpansion.old_face A s.src s.dst) m
  rw [mapPath_append] at hm
  exact .trans hm s.moves

theorem source_count {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    [Finite (Vertex A)] (f : V → W) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (b : W)
    (s : Insertion f p q b) :
    Nat.card (Vertex (SourceExpansion.expansion A s.src s.dst)) = Nat.card (Vertex A) + 1 :=
  SourceExpansion.expansion_vertex_count A s.src s.dst s.face

theorem source_finite {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    [Finite (Vertex A)] (f : V → W) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (b : W)
    (s : Insertion f p q b) : Finite (Vertex (SourceExpansion.expansion A s.src s.dst)) :=
  SourceExpansion.expansion_vertices_finite A s.src s.dst s.face

theorem source_dimension {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (b : W)
    (s : Insertion f p q b) (hd : SimplicialImages.AtMostTwo A) :
    SimplicialImages.AtMostTwo (SourceExpansion.expansion A s.src s.dst) :=
  SourceExpansion.expansion_dimension A s.src s.dst hd

def sourcePaths {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (b : W)
    (s : Insertion f p q b) (r : Vertex A) (paths : ∀ x : Vertex A, Path A r.val x.val)
    (x : Vertex (SourceExpansion.expansion A s.src s.dst)) :
    Path (SourceExpansion.expansion A s.src s.dst) (SourceExpansion.old r.val) x.val :=
  SourceExpansion.expansionPaths A s.src s.dst s.face r paths x

theorem source_span {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (b : W)
    (s : Insertion f p q b) {r : V} (g : Path A r r)
    (hs : CycleSpan A (PathChains.chain (PathChains.trivialTransport A) g)) :
    CycleSpan (SourceExpansion.expansion A s.src s.dst)
      (PathChains.chain (PathChains.trivialTransport _) (mapPath SourceExpansion.old (SourceExpansion.old_face A s.src s.dst) g)) :=
  cycle_span_expanded_loop A s.src s.dst s.face g hs

theorem retained_path {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (q : Path B (f u) (f v)) (b : W)
    (s : Insertion f p q b) {i j : V} (g : Path A i j) :
    mapPath (SourceExpansion.extend f b) s.face_map
      (mapPath SourceExpansion.old (SourceExpansion.old_face A s.src s.dst) g) = mapPath f hf g := by
  have htri : ({b,f s.src,f s.dst} : Finset W) ∈ B := by
    have hh := image_mem (SourceExpansion.extend f b) s.face_map _ (SourceExpansion.attached_face A s.src s.dst)
    simp only [Finset.image_insert,Finset.image_singleton] at hh
    exact hh
  exact retained_expansion_path f hf s.src s.dst b htri g

theorem retained_value {K : Type*} [Field K] {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) (tau : Transport (K := K) B) {u v : V}
    (p : Path A u v) (q : Path B (f u) (f v)) (b : W) (s : Insertion f p q b) {i j : V} (g : Path A i j) :
    value tau (mapPath (SourceExpansion.extend f b) s.face_map
      (mapPath SourceExpansion.old (SourceExpansion.old_face A s.src s.dst) g)) = value tau (mapPath f hf g) :=
  congrArg (value tau) (retained_path f hf p q b s g)



def demoLabels (x : Fin 2) : Fin 3 := ⟨2*x.val,by have h := x.isLt; omega⟩

def demoPath : Path (⊤ : PreAbstractSimplicialComplex (Fin 2)) 0 1 := single (Finset.insert_nonempty _ _)

theorem demo_face_map : (⊤ : PreAbstractSimplicialComplex (Fin 2)).map demoLabels ≤
    (⊤ : PreAbstractSimplicialComplex (Fin 3)) := by rintro s ⟨t,ht,rfl⟩; exact ht.image _

def demoUpdate := insertHead demoLabels demo_face_map demoPath 1 2
  (Finset.insert_nonempty _ _) (.refl 2 (Finset.singleton_nonempty _)) (by rfl)

theorem demo_inserted_source_trace : vertices demoUpdate.upper =
    [SourceExpansion.old 0,SourceExpansion.fresh 0,SourceExpansion.old 1] := by decide

theorem demo_actual_target_trace : vertices (mapPath (SourceExpansion.extend demoLabels 1)
    demoUpdate.face_map demoUpdate.upper) = [0,1,2] := by decide

theorem demo_active_vertex_count : Nat.card (Vertex (SourceExpansion.expansion
    (⊤ : PreAbstractSimplicialComplex (Fin 2)) demoUpdate.src demoUpdate.dst)) = 3 := by
  have hA : Nat.card (Vertex (⊤ : PreAbstractSimplicialComplex (Fin 2))) = 2 := by
    let e : Vertex (⊤ : PreAbstractSimplicialComplex (Fin 2)) ≃ Fin 2 :=
      { toFun := Subtype.val, invFun := fun x => ⟨x,Finset.singleton_nonempty _⟩,
        left_inv := fun _ => Subtype.ext rfl, right_inv := fun _ => rfl }
    rw [Nat.card_congr e]; simp
  rw [source_count demoLabels demoPath _ 1 demoUpdate,hA]

def demoConstant : Path (⊤ : PreAbstractSimplicialComplex (Fin 2)) 0 0 := .refl 0 (Finset.singleton_nonempty _)

def demoBacktrack := insertBacktrack demoLabels demo_face_map demoConstant 0 1
  (Finset.insert_nonempty _ _) (.refl 0 (Finset.singleton_nonempty _))
  (.refl 0 (Finset.singleton_nonempty _)) (by rfl)

theorem demo_leaf_backtrack : vertices demoBacktrack.upper =
    [SourceExpansion.old 0,SourceExpansion.fresh 0,SourceExpansion.old 0] ∧
    vertices (mapPath (SourceExpansion.extend demoLabels 1) demoBacktrack.face_map demoBacktrack.upper) = [0,1,0] := by
  constructor <;> decide

def demoStutter := insertStutter demoLabels demo_face_map demoConstant 0
  (Finset.singleton_nonempty _) (.refl 0 (Finset.singleton_nonempty _))
  (.refl 0 (Finset.singleton_nonempty _)) (by rfl)

theorem demo_stutter_still_has_fresh_vertex : vertices demoStutter.upper =
    [SourceExpansion.old 0,SourceExpansion.fresh 0,SourceExpansion.old 0] ∧
    SourceExpansion.old (0 : Fin 2) ≠ SourceExpansion.fresh 0 := by
  constructor <;> decide

theorem wrong_fresh_label_rejected :
    vertices (mapPath (SourceExpansion.extend demoLabels 0)
      (SourceExpansion.extend_face demoLabels demo_face_map 0 1 0 (Finset.insert_nonempty _ _)) demoUpdate.upper) ≠ [0,1,2] := by decide

theorem missing_target_triangle_rejected :
    ¬ (SourceExpansion.expansion cycleComplex 0 1).map
      (SourceExpansion.extend (id : Fin 3 → Fin 3) 2) ≤ cycleComplex :=
  SourceMoveSimulation.missing_insertion_triangle_rejected

theorem incorrect_fresh_vertex_count_rejected :
    Nat.card (Vertex (SourceExpansion.expansion (⊤ : PreAbstractSimplicialComplex (Fin 2))
      demoUpdate.src demoUpdate.dst)) ≠ 2 := by rw [demo_active_vertex_count]; decide

def desiredInserted : Path (⊤ : PreAbstractSimplicialComplex (Fin 3)) (demoLabels 0) (demoLabels 1) :=
  .cons (v := 1) (Finset.insert_nonempty _ _) (.cons (Finset.insert_nonempty _ _)
    (.refl (demoLabels 1) (Finset.singleton_nonempty _)))

theorem inverse_direction_stale_upper_rejected :
    ¬ Realizes demoLabels demo_face_map demoPath desiredInserted := by
  -- The intended inserted middle label is explicitly 1, not the old source endpoint.
  intro h
  have hh := congrArg vertices h
  change [0,2] = [0,1,2] at hh
  contradiction


end D2RelationGap.InsertionTraceUpdate
