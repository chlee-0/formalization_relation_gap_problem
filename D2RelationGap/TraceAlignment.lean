import D2RelationGap.StutterTrace

/-!
Actual source cuts extracted from literal normalized mapped traces.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. Local source move simulation, its finite history and
original-character/geometric adequacy remain separate obligations.
-/
noncomputable section
namespace D2RelationGap.TraceAlignment
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops SourceRefinement StutterTrace
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

theorem normalize_cons_vertices {A : PreAbstractSimplicialComplex V} {u w v : V}
    (h : ({u,w} : Finset V) ∈ A) (p : Path A w v) :
    vertices (StutterTrace.normalize (.cons h p)) =
      if u = w then vertices (StutterTrace.normalize p) else u :: vertices (StutterTrace.normalize p) := by
  by_cases he : u = w
  · subst w; simp [StutterTrace.normalize]
  · simp [StutterTrace.normalize,he,vertices]

theorem imageTrace_cons_vertices {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B)
    {u w v : V} (h : ({u,w} : Finset V) ∈ A) (p : Path A w v) :
    vertices (imageTrace f hf (.cons h p)) =
      if f u = f w then vertices (imageTrace f hf p) else f u :: vertices (imageTrace f hf p) :=
  normalize_cons_vertices _ _

/-- All fields are actual SOURCE data, with literal decomposition and target traces. -/
structure FirstSplit {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (b : W) (rest : List W) where
  src : V
  dst : V
  before : Path A u src
  face : ({src,dst} : Finset V) ∈ A
  suffix : Path A dst v
  decomposition : p = append before (.cons face suffix)
  before_labels : ∀ x ∈ vertices before, f x = f u
  src_label : f src = f u
  dst_label : f dst = b
  noncollapsed : f src ≠ f dst
  suffix_trace : vertices (imageTrace f hf suffix) = b :: rest

/-- Find the first ACTUAL noncollapsed source edge by finite path recursion;
collapsed source vertices are retained in the computed prefix. -/
def firstSplit {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (b : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = f u :: b :: rest) : FirstSplit f hf p b rest := by
  induction p with
  | refl u hu =>
    have hh : ([] : List W) = b :: rest := List.cons.inj he |>.2
    cases hh
  | @cons u w v h p ih =>
    by_cases hc : f u = f w
    · have ht : vertices (imageTrace f hf p) = f w :: b :: rest := by
        rw [imageTrace_cons_vertices,ite_eq_left hc] at he
        simpa only [hc] using he
      let s := ih ht
      refine ⟨s.src,s.dst,.cons h s.before,s.face,s.suffix,?_,?_,?_,s.dst_label,s.noncollapsed,s.suffix_trace⟩
      · change Path.cons h p = Path.cons h (append s.before (.cons s.face s.suffix))
        exact congrArg (Path.cons h) s.decomposition
      · intro x hx
        simp only [vertices,List.mem_cons] at hx
        rcases hx with rfl | hx
        · rfl
        · exact (s.before_labels x hx).trans hc.symm
      · exact s.src_label.trans hc.symm
    · have ht : vertices (imageTrace f hf p) = b :: rest := by
        rw [imageTrace_cons_vertices,ite_eq_right hc] at he
        exact List.cons.inj he |>.2
      have hw : f w = b := Option.some.inj (by simpa only [vertices_head,List.head?_cons] using congrArg List.head? ht)
      refine ⟨u,w,.refl u (startActive (.cons h p)),h,p,rfl,?_,rfl,hw,hc,ht⟩
      intro x hx
      have hx' : x = u := by simpa only [vertices,List.mem_singleton] using hx
      subst x
      rfl

theorem firstSplit_target_face {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V}
    (p : Path A u v) (b : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = f u :: b :: rest) : ({f u,b} : Finset W) ∈ B := by
  let s := firstSplit f hf p b rest he
  have hh := image_mem f hf _ s.face
  simpa only [Finset.image_insert,Finset.image_singleton,s.src_label,s.dst_label] using hh

theorem firstSplit_prefix_can_be_shortened {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V}
    (p : Path A u v) (b : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = f u :: b :: rest) :
    ∀ x ∈ vertices (firstSplit f hf p b rest he).before,
      f x = f (firstSplit f hf p b rest he).src := by
  intro x hx
  exact ((firstSplit f hf p b rest he).before_labels x hx).trans
    (firstSplit f hf p b rest he).src_label.symm

theorem constant_before_trace {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B)
    {u x v : V} (pre : Path A u x) (post : Path A x v)
    (hl : ∀ z ∈ vertices pre, f z = f x) :
    vertices (imageTrace f hf (append pre post)) = vertices (imageTrace f hf post) := by
  induction pre with
  | refl => rfl
  | @cons u w x h pre ih =>
    have hp : ∀ z ∈ vertices pre, f z = f x := fun z hz => hl z (by simp [vertices,hz])
    have hu : f u = f x := hl u (by simp [vertices])
    have hw : f w = f x := hp w (CollapsedSegments.start_mem_vertices pre)
    change vertices (imageTrace f hf (.cons h (append pre post))) = _
    rw [imageTrace_cons_vertices,ite_eq_left (hu.trans hw.symm)]
    exact ih post hp

/-- A cut at ANY normalized vertex, with actual source paths on both sides. -/
structure Cut {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v)
    (front : List W) (boundary : W) (rest : List W) where
  node : V
  before : Path A u node
  after : Path A node v
  decomposition : p = append before after
  node_label : f node = boundary
  before_trace : vertices (imageTrace f hf before) = front ++ [boundary]
  after_trace : vertices (imageTrace f hf after) = boundary :: rest

def extendCut {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v)
    (b : W) (tail : List W) (front : List W) (boundary : W) (rest : List W)
    (s : FirstSplit f hf p b tail) (t : Cut f hf s.suffix front boundary rest) :
    Cut f hf p (f u :: front) boundary rest := by
  refine ⟨t.node,append s.before (.cons s.face t.before),t.after,?_,t.node_label,?_,t.after_trace⟩
  · calc
      p = append s.before (.cons s.face s.suffix) := s.decomposition
      _ = append s.before (.cons s.face (append t.before t.after)) :=
        congrArg (fun q => append s.before (.cons s.face q)) t.decomposition
      _ = append (append s.before (.cons s.face t.before)) t.after := by rw [append_assoc]; rfl
  · have hl : ∀ z ∈ vertices s.before, f z = f s.src := fun z hz =>
      (s.before_labels z hz).trans s.src_label.symm
    rw [constant_before_trace f hf s.before (.cons s.face t.before) hl,
      imageTrace_cons_vertices,ite_eq_right s.noncollapsed,s.src_label,t.before_trace]
    rfl

/-- Recursively construct a cut from the EXACT normalized trace; no lifting or
spanning assumption is part of this input. -/
def cut {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v)
    (front : List W) (boundary : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = front ++ boundary :: rest) : Cut f hf p front boundary rest := by
  induction front generalizing u with
  | nil =>
    have hu : f u = boundary := Option.some.inj (by simpa only [vertices_head,List.nil_append,List.head?_cons] using congrArg List.head? he)
    refine ⟨u,.refl u (startActive p),p,rfl,hu,?_,?_⟩
    · simp only [imageTrace,mapPath,StutterTrace.normalize,vertices,List.nil_append,hu]
    · simpa only [List.nil_append] using he
  | cons a front ih =>
    have hu : f u = a := Option.some.inj (by simpa only [vertices_head,List.cons_append,List.head?_cons] using congrArg List.head? he)
    cases front with
    | nil =>
      have ht : vertices (imageTrace f hf p) = f u :: boundary :: rest := by simpa only [List.cons_append,List.nil_append,hu] using he
      let s := firstSplit f hf p boundary rest ht
      have hq : vertices (imageTrace f hf s.suffix) = [] ++ boundary :: rest := s.suffix_trace
      let t := ih s.suffix hq
      simpa only [hu] using extendCut f hf p boundary rest [] boundary rest s t
    | cons b tail =>
      have ht : vertices (imageTrace f hf p) = f u :: b :: (tail ++ boundary :: rest) := by
        simpa only [List.cons_append,hu] using he
      let s := firstSplit f hf p b (tail ++ boundary :: rest) ht
      have hq : vertices (imageTrace f hf s.suffix) = (b :: tail) ++ boundary :: rest := s.suffix_trace
      let t := ih s.suffix hq
      simpa only [hu] using extendCut f hf p b (tail ++ boundary :: rest) (b :: tail) boundary rest s t

structure TwoSplit {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (b c : W) (rest : List W) where
  first : FirstSplit f hf p b (c :: rest)
  second : FirstSplit f hf first.suffix c rest

def twoSplit {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (b c : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = f u :: b :: c :: rest) : TwoSplit f hf p b c rest := by
  let s := firstSplit f hf p b (c :: rest) he
  have ht : vertices (imageTrace f hf s.suffix) = f s.dst :: c :: rest := by
    simpa only [s.dst_label] using s.suffix_trace
  exact ⟨s,firstSplit f hf s.suffix c rest ht⟩

theorem twoSplit_middle_can_be_shortened {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V}
    (p : Path A u v) (b c : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = f u :: b :: c :: rest) :
    ∀ z ∈ vertices (twoSplit f hf p b c rest he).second.before,
      f z = f (twoSplit f hf p b c rest he).second.src := by
  intro z hz
  let s := twoSplit f hf p b c rest he
  exact (s.second.before_labels z hz).trans s.second.src_label.symm

def cutOfRealizes {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (q : Path B (f u) (f v))
    (front : List W) (boundary : W) (rest : List W) (h : Realizes f hf p q)
    (ht : vertices (StutterTrace.normalize q) = front ++ boundary :: rest) : Cut f hf p front boundary rest :=
  cut f hf p front boundary rest ((congrArg vertices h).trans ht)

theorem twoSplit_decomposition {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V}
    (p : Path A u v) (b c : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = f u :: b :: c :: rest) :
    p = append (twoSplit f hf p b c rest he).first.before
      (.cons (twoSplit f hf p b c rest he).first.face
        (append (twoSplit f hf p b c rest he).second.before
          (.cons (twoSplit f hf p b c rest he).second.face
            (twoSplit f hf p b c rest he).second.suffix))) := by
  let s := twoSplit f hf p b c rest he
  exact s.first.decomposition.trans
    (congrArg (fun q => append s.first.before (.cons s.first.face q)) s.second.decomposition)

theorem twoSplit_target_triangle {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V}
    (p : Path A u v) (b c : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = f u :: b :: c :: rest)
    (ht : ({f u,b,c} : Finset W) ∈ B) :
    ({f (twoSplit f hf p b c rest he).first.src,
      f (twoSplit f hf p b c rest he).second.src,
      f (twoSplit f hf p b c rest he).second.dst} : Finset W) ∈ B := by
  let s := twoSplit f hf p b c rest he
  change ({f s.first.src,f s.second.src,f s.second.dst} : Finset W) ∈ B
  rw [s.first.src_label,s.second.src_label,s.first.dst_label,s.second.dst_label]
  exact ht

theorem normalize_append_vertices {A : PreAbstractSimplicialComplex V} {u v w : V}
    (pre : Path A u v) (post : Path A v w) :
    vertices (StutterTrace.normalize (append pre post)) =
      steps (StutterTrace.normalize pre) ++ vertices (StutterTrace.normalize post) := by
  induction pre with
  | refl => rfl
  | @cons u x v h pre ih =>
    by_cases he : u = x
    · subst x; simpa [append,StutterTrace.normalize] using ih post
    · simpa [append,StutterTrace.normalize,he,vertices,steps] using congrArg (List.cons u) (ih post)

theorem vertices_eq_start_tail {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    vertices p = u :: (vertices p).tail := by
  cases p <;> rfl

/-- Match an arbitrary ACTUAL target prefix/postfix context from Realizes,
without assuming the desired source cut or its constant blocks. -/
def cutAtTargetContext {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (a : W)
    (pre : Path B (f u) a) (post : Path B a (f v)) (h : Realizes f hf p (append pre post)) :
    Cut f hf p (steps (StutterTrace.normalize pre)) a (vertices (StutterTrace.normalize post)).tail := by
  apply cutOfRealizes f hf p (append pre post) _ a _ h
  rw [normalize_append_vertices,vertices_eq_start_tail (StutterTrace.normalize post)]
  rfl

theorem cutAtTargetContext_before_trace {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V}
    (p : Path A u v) (a : W) (pre : Path B (f u) a) (post : Path B a (f v))
    (h : Realizes f hf p (append pre post)) :
    vertices (imageTrace f hf (cutAtTargetContext f hf p a pre post h).before) =
      vertices (StutterTrace.normalize pre) :=
  (cutAtTargetContext f hf p a pre post h).before_trace.trans (vertices_eq_steps_end _).symm

/-- Apply the existing SOURCE block shortcut to the middle computed by twoSplit.
This prepares a local triangle/backtrack operation; it does not yet perform it. -/
def shortenExtractedMiddle {A : PreAbstractSimplicialComplex V} {B : PreAbstractSimplicialComplex W}
    (f : V → W) (hf : A.map f ≤ B) {u v : V} (p : Path A u v) (b c : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = f u :: b :: c :: rest) :
    let s := twoSplit f hf p b c rest he
    let mid := s.second.before
    let hi := TriangleAttachment.identity_face_map (MappedCap.cap_inclusion A s.second.src mid)
    Moves (mapPath id hi p)
      (append (mapPath id hi (append s.first.before (single s.first.face)))
        (append (CollapsedSegments.shortcut A mid) (mapPath id hi (.cons s.second.face s.second.suffix)))) := by
  let s := twoSplit f hf p b c rest he
  let pre := append s.first.before (single s.first.face)
  let post := Path.cons s.second.face s.second.suffix
  have hp : p = append pre (append s.second.before post) := by
    exact (twoSplit_decomposition f hf p b c rest he).trans (by rw [append_assoc]; rfl)
  have hm := CollapsedSegments.contextual_shortcut_moves A pre s.second.before post
  have heq := congrArg (mapPath id (TriangleAttachment.identity_face_map
    (MappedCap.cap_inclusion A s.second.src s.second.before))) hp
  dsimp only
  exact heq.symm ▸ hm

theorem extracted_middle_shortening_preserves_trace {A : PreAbstractSimplicialComplex V}
    {B : PreAbstractSimplicialComplex W} (f : V → W) (hf : A.map f ≤ B) {u v : V}
    (p : Path A u v) (b c : W) (rest : List W)
    (he : vertices (imageTrace f hf p) = f u :: b :: c :: rest) :
    let s := twoSplit f hf p b c rest he
    let hl := twoSplit_middle_can_be_shortened f hf p b c rest he
    let hC := MappedCap.cap_map f hf s.second.src s.second.before hl
    let hi := TriangleAttachment.identity_face_map (MappedCap.cap_inclusion A s.second.src s.second.before)
    imageTrace f hC (mapPath id hi p) = imageTrace f hC
      (append (mapPath id hi (append s.first.before (single s.first.face)))
        (append (CollapsedSegments.shortcut A s.second.before) (mapPath id hi (.cons s.second.face s.second.suffix)))) := by
  let s := twoSplit f hf p b c rest he
  let pre := append s.first.before (single s.first.face)
  let post := Path.cons s.second.face s.second.suffix
  have hp : p = append pre (append s.second.before post) :=
    (twoSplit_decomposition f hf p b c rest he).trans (by rw [append_assoc]; rfl)
  have hm := contextual_segment_shortening_preserves_trace f hf pre s.second.before post
    (twoSplit_middle_can_be_shortened f hf p b c rest he)
  have heq := congrArg (fun q => imageTrace f
    (MappedCap.cap_map f hf s.second.src s.second.before (twoSplit_middle_can_be_shortened f hf p b c rest he))
    (mapPath id (TriangleAttachment.identity_face_map (MappedCap.cap_inclusion A s.second.src s.second.before)) q)) hp
  exact heq.trans hm

def demoPath : Path (PolygonSource.polygon 3) 0 5 :=
  .cons (v := 1) (by simpa [PolygonSource.next] using PolygonSource.pair_face 3 0)
    (.cons (v := 2) (by simpa [PolygonSource.next] using PolygonSource.pair_face 3 1)
      (.cons (v := 3) (by simpa [PolygonSource.next] using PolygonSource.pair_face 3 2)
        (.cons (v := 4) (by simpa [PolygonSource.next] using PolygonSource.pair_face 3 3)
          (.cons (v := 5) (by simpa [PolygonSource.next] using PolygonSource.pair_face 3 4)
            (.refl 5 (PolygonSource.singleton_face 3 5))))))

def demoLabels (v : Fin 6) : Fin 3 := ⟨v.val / 2,by have hv := v.isLt; omega⟩

theorem demo_face_map : (PolygonSource.polygon 3).map demoLabels ≤
    (⊤ : PreAbstractSimplicialComplex (Fin 3)) := by
  rintro s ⟨t,ht,rfl⟩
  exact (PolygonSource.polygon 3).isRelLowerSet_faces ht |>.1.image _

theorem demo_trace : vertices (imageTrace demoLabels demo_face_map demoPath) = [0,1,2] := by
  rfl

theorem demo_cycle_face_map : (PolygonSource.polygon 3).map demoLabels ≤ cycleComplex := by
  rintro s ⟨t,ht,rfl⟩
  exact ⟨(PolygonSource.polygon 3).isRelLowerSet_faces ht |>.1.image _,
    Finset.card_image_le.trans (PolygonSource.face_card_le_two 3 t ht)⟩

theorem demo_cycle_trace : vertices (imageTrace demoLabels demo_cycle_face_map demoPath) = [0,1,2] := by rfl

def demoFirst := firstSplit demoLabels demo_face_map demoPath 1 [2] demo_trace
def demoTwo := twoSplit demoLabels demo_face_map demoPath 1 2 [] demo_trace
def demoCut := cut demoLabels demo_face_map demoPath [0] 1 [2] demo_trace

def demoTargetPre : Path (⊤ : PreAbstractSimplicialComplex (Fin 3)) (demoLabels 0) 1 :=
  single (Finset.insert_nonempty _ _)
def demoTargetPost : Path (⊤ : PreAbstractSimplicialComplex (Fin 3)) 1 (demoLabels 5) :=
  single (Finset.insert_nonempty _ _)
theorem demo_realizes : Realizes demoLabels demo_face_map demoPath (append demoTargetPre demoTargetPost) := by rfl
def demoContextCut := cutAtTargetContext demoLabels demo_face_map demoPath 1 demoTargetPre demoTargetPost demo_realizes

theorem demo_extraction : demoFirst.src = 1 ∧ demoFirst.dst = 2 ∧
    vertices demoFirst.before = [0,1] ∧ demoTwo.second.src = 3 ∧ demoTwo.second.dst = 4 ∧
    vertices demoTwo.second.before = [2,3] ∧ demoCut.node = 2 ∧
    vertices demoCut.before = [0,1,2] := by
  decide

theorem immediate_source_head_rejected : demoFirst.src ≠ 0 ∧ demoCut.node ≠ 1 := by decide

theorem demo_context_cut : demoContextCut.node = 2 ∧ vertices demoContextCut.before = [0,1,2] ∧
    vertices demoContextCut.after = [2,3,4,5] := by decide

theorem constant_middle_does_not_identify_source_vertices :
    demoTwo.first.dst ≠ demoTwo.second.src ∧
    demoLabels demoTwo.first.dst = demoLabels demoTwo.second.src := by decide

theorem wrong_normalized_next_vertex_rejected :
    vertices (imageTrace demoLabels demo_face_map demoPath) ≠ [0,2,1] := by rw [demo_trace]; decide

theorem empty_trace_cannot_supply_first_edge :
    ¬ (vertices (imageTrace (fun _ : Fin 3 => (0 : Fin 1))
      (B := (⊤ : PreAbstractSimplicialComplex (Fin 1)))
      (by rintro s ⟨t,ht,rfl⟩; exact ht.1.image _) CollapsedSegments.distinctSegment) = [0,0]) := by
  decide

theorem two_target_edges_do_not_supply_triangle :
    ({0,1} : Finset (Fin 3)) ∈ cycleComplex ∧ ({1,2} : Finset (Fin 3)) ∈ cycleComplex ∧
    ({0,1,2} : Finset (Fin 3)) ∉ cycleComplex := by
  constructor
  · constructor <;> simp
  constructor
  · constructor <;> simp
  intro h
  have hc : ({0,1,2} : Finset (Fin 3)).card ≤ 2 := h.2
  norm_num at hc

end D2RelationGap.TraceAlignment
