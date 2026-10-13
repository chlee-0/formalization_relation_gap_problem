import D2RelationGap.LocalTraceUpdate
import D2RelationGap.ComplexFox

/-!
The actual three-edge rose used as the base of the collared presentation compiler.
Credit: OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
Relator collars and their actual boundary/cycle comparison are separate obligations.
-/
noncomputable section
namespace D2RelationGap.PresentationRose
open Targets OrientedSimplices SimplicialTransport EdgePaths BasedLoops SourceRefinement
open FoxSemantics FoxRank

abbrev Ambient := Fin 11

def index : Gen → ℕ
  | .x1 => 0
  | .a1 => 1
  | .x2 => 2
  | .a2 => 3
  | .s => 4

def b (g : Gen) : Ambient := ⟨2*index g+1,by cases g <;> decide⟩
def c (g : Gen) : Ambient := ⟨2*index g+2,by cases g <;> decide⟩

def petal (g : Gen) : Fin 3 → Finset Ambient
  | 0 => {0,b g}
  | 1 => {b g,c g}
  | 2 => {c g,0}

def rose : PreAbstractSimplicialComplex Ambient where
  faces := {s | s.Nonempty ∧ ∃ (g : Gen) (i : Fin 3), s ⊆ petal g i}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    obtain ⟨g,i,hi⟩ := hs.2
    exact ⟨ht,g,i,hts.trans hi⟩

instance faceDecidable (s : Finset Ambient) : Decidable (s ∈ rose) :=
  inferInstanceAs (Decidable (s.Nonempty ∧ ∃ (g : Gen) (i : Fin 3), s ⊆ petal g i))

theorem petal_face (g : Gen) (i : Fin 3) : petal g i ∈ rose := by
  refine ⟨?_,g,i,Finset.Subset.refl _⟩
  fin_cases i <;> exact Finset.insert_nonempty _ _

theorem singleton_face (x : Ambient) : ({x} : Finset Ambient) ∈ rose := by
  fin_cases x <;> decide

def complex : AbstractSimplicialComplex Ambient where
  toPreAbstractSimplicialComplex := rose
  singleton_mem := singleton_face

def vertexEquiv : Vertex rose ≃ Ambient where
  toFun := Subtype.val
  invFun x := ⟨x,singleton_face x⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

theorem active_vertex_count : Nat.card (Vertex rose) = 11 := by
  rw [Nat.card_congr vertexEquiv,Nat.card_fin]

theorem dimension_at_most_one (s : Finset Ambient) (hs : s ∈ rose) : s.card ≤ 2 := by
  obtain ⟨g,i,hi⟩ := hs.2
  apply (Finset.card_le_card hi).trans
  fin_cases i <;> cases g <;> decide

instance triangles_empty : IsEmpty (Triangle rose) := ⟨fun t => by
  have hh := dimension_at_most_one (triangleFace t) t.face
  rw [triangleFace_card] at hh
  omega⟩

abbrev root : Vertex rose := ⟨0,singleton_face 0⟩

theorem root_edge (x : Ambient) : ({0,x} : Finset Ambient) ∈ rose := by
  fin_cases x <;> decide

def rootPaths (x : Vertex rose) : Path rose 0 x.val := single (root_edge x.val)

instance roseLoopGroup : Group (Loop rose root) := loopGroup rose root

def generatorLoop (g : Gen) : Path rose 0 0 :=
  .cons (petal_face g 0) (.cons (petal_face g 1) (.cons (petal_face g 2) (.refl 0 (singleton_face 0))))

/-- Only the closing rose edge carries the chosen generator unit. -/
def closingGen (x : Ambient) : Option Gen :=
  match x.val with
  | 2 => some .x1
  | 4 => some .a1
  | 6 => some .x2
  | 8 => some .a2
  | 10 => some .s
  | _ => none

def unit {K : Type*} [Field K] (q : Gen → Kˣ) (u v : Ambient) : Kˣ :=
  if u = 0 then
    match closingGen v with | some g => (q g)⁻¹ | none => 1
  else if v = 0 then
    match closingGen u with | some g => q g | none => 1
  else 1

theorem unit_flat {K : Type*} [Field K] (q : Gen → Kˣ) (u v w : Ambient)
    (ht : ({u,v,w} : Finset Ambient) ∈ rose) : unit q u v * unit q v w = unit q u w := by
  obtain ⟨g,i,hi⟩ := ht.2
  have hu := hi (show u ∈ ({u,v,w} : Finset Ambient) by simp)
  have hv := hi (show v ∈ ({u,v,w} : Finset Ambient) by simp)
  have hw := hi (show w ∈ ({u,v,w} : Finset Ambient) by simp)
  fin_cases i <;> cases g <;> simp only [petal,b,c,index] at hu hv hw
  all_goals
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv hw
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    all_goals simp [unit,closingGen]

def transport {K : Type*} [Field K] (q : Gen → Kˣ) : Transport (K := K) rose :=
  ⟨unit q,unit_flat q⟩

theorem generator_value {K : Type*} [Field K] (q : Gen → Kˣ) (g : Gen) :
    value (transport q) (generatorLoop g) = q g := by
  cases g <;> simp [generatorLoop,value,transport,unit,closingGen,b,c,index]

/-- No raw word reduction is performed in the compiler path. -/
def letterPath (l : Letter) : Path rose 0 0 :=
  if l.positive then generatorLoop l.gen else reverse (generatorLoop l.gen)

def wordPath : Word → Path rose 0 0
  | [] => .refl 0 (singleton_face 0)
  | l :: w => append (letterPath l) (wordPath w)

def evalLoops : F →* Loop rose root := FreeGroup.lift (fun g => Quotient.mk _ (generatorLoop g))

theorem class_letter (l : Letter) : (Quotient.mk _ (letterPath l) : Loop rose root) = evalLoops (freeLetter l) := by
  rcases l with ⟨g,h⟩
  cases h
  · change (Quotient.mk _ (reverse (generatorLoop g)) : Loop rose root) = evalLoops ((FreeGroup.of g)⁻¹)
    rw [map_inv]
    change (Quotient.mk _ (generatorLoop g) : Loop rose root)⁻¹ =
      (FreeGroup.lift _ (FreeGroup.of g))⁻¹
    rw [FreeGroup.lift_apply_of]
  · change (Quotient.mk _ (generatorLoop g) : Loop rose root) = FreeGroup.lift _ (FreeGroup.of g)
    rw [FreeGroup.lift_apply_of]

theorem class_word (w : Word) : (Quotient.mk _ (wordPath w) : Loop rose root) = evalLoops (freeWord w) := by
  induction w with
  | nil => rw [freeWord_nil,map_one]; rfl
  | cons l w ih =>
    calc
      (Quotient.mk _ (wordPath (l::w)) : Loop rose root) =
          (Quotient.mk _ (letterPath l) : Loop rose root) * Quotient.mk _ (wordPath w) := rfl
      _ = evalLoops (freeLetter l) * evalLoops (freeWord w) :=
        congrArg₂ (fun x y : Loop rose root => x*y) (class_letter l) ih
      _ = evalLoops (freeWord (l::w)) := by rw [freeWord_cons,map_mul]

def generatorUnit (g : Gen) : ℂˣ := ComplexCharacter.character (quotientMap (FreeGroup.of g))
def originalTransport : Transport (K := ℂ) rose := transport generatorUnit

theorem original_character_agreement :
    (holonomy originalTransport root).comp evalLoops = ComplexCharacter.character.comp quotientMap := by
  apply FreeGroup.ext_hom
  intro g
  change value originalTransport (generatorLoop g) = generatorUnit g
  exact generator_value generatorUnit g

theorem word_value (w : Word) : value originalTransport (wordPath w) =
    ComplexCharacter.character (quotientMap (freeWord w)) := by
  have hh := DFunLike.congr_fun original_character_agreement (freeWord w)
  change holonomy originalTransport root (evalLoops (freeWord w)) = _ at hh
  exact (congrArg (holonomy originalTransport root) (class_word w)).trans hh

theorem x1_detected : ((value originalTransport (generatorLoop .x1) : ℂˣ) : ℂ) = -1 := by
  exact (congrArg (fun z : ℂˣ => (z : ℂ)) (generator_value generatorUnit .x1)).trans ComplexCharacter.rho_x1

/-- Literal source edges stay noncollapsed even when a raw word freely cancels. -/
def Noncollapsed {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    {u v : V} : Path A u v → Prop
  | .refl _ _ => True
  | @Path.cons _ _ _ x y _ _ p => x ≠ y ∧ Noncollapsed p

theorem noncollapsed_append {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    {u v w : V} (p : Path A u v) (q : Path A v w) (hp : Noncollapsed p) (hq : Noncollapsed q) :
    Noncollapsed (append p q) := by
  induction p with
  | refl => exact hq
  | cons h p ih => exact ⟨hp.1,ih q hp.2 hq⟩

theorem noncollapsed_reverse {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    {u v : V} (p : Path A u v) (hp : Noncollapsed p) : Noncollapsed (reverse p) := by
  induction p with
  | refl => trivial
  | cons h p ih => exact noncollapsed_append _ _ (ih hp.2) ⟨hp.1.symm,True.intro⟩

theorem generator_noncollapsed (g : Gen) : Noncollapsed (generatorLoop g) := by
  cases g <;> simp [Noncollapsed,generatorLoop,b,c,index]

theorem letter_noncollapsed (l : Letter) : Noncollapsed (letterPath l) := by
  rcases l with ⟨g,h⟩
  cases h
  · exact noncollapsed_reverse _ (generator_noncollapsed g)
  · exact generator_noncollapsed g

theorem word_noncollapsed (w : Word) : Noncollapsed (wordPath w) := by
  induction w with
  | nil => trivial
  | cons l w ih => exact noncollapsed_append _ _ (letter_noncollapsed l) ih

theorem length_append {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    {u v w : V} (p : Path A u v) (q : Path A v w) :
    PolygonSource.length (append p q) = PolygonSource.length p + PolygonSource.length q := by
  induction p with
  | refl => simp [append,PolygonSource.length]
  | cons h p ih => simp [append,PolygonSource.length,ih,Nat.add_assoc,Nat.add_comm]

theorem length_reverse {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    {u v : V} (p : Path A u v) : PolygonSource.length (reverse p) = PolygonSource.length p := by
  induction p with
  | refl => rfl
  | cons h p ih => simp [reverse,length_append,single,PolygonSource.length,ih]

theorem letter_length (l : Letter) : PolygonSource.length (letterPath l) = 3 := by
  rcases l with ⟨g,h⟩
  cases h
  · rw [letterPath]; simp only [Bool.false_eq_true,ite_eq_right,not_false_eq_true,length_reverse]; rfl
  · rfl

theorem word_length (w : Word) : PolygonSource.length (wordPath w) = 3*w.length := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [wordPath,length_append,letter_length,ih,List.length_cons]; omega

theorem nonempty_word_length (w : Word) (hw : w ≠ []) : 3 ≤ PolygonSource.length (wordPath w) := by
  rw [word_length]
  have hh : 0 < w.length := List.length_pos_iff_ne_nil.mpr hw
  omega

theorem node_distinct {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    {u v : V} (p : Path A u v) (hp : Noncollapsed p) (k : ℕ) (hk : k < PolygonSource.length p) :
    PolygonSource.node p k ≠ PolygonSource.node p (k+1) := by
  induction p generalizing k with
  | refl => simp only [PolygonSource.length] at hk; omega
  | cons h p ih =>
    cases k with
    | zero => simpa only [PolygonSource.node,PolygonSource.node_zero] using hp.1
    | succ k => exact ih hp.2 k (by simp only [PolygonSource.length] at hk; omega)

/-- The actual root--b edge reads the coefficient of one rose generator. -/
def firstEdge (g : Gen) : Edge rose :=
  ⟨0,b g,by cases g <;> decide,petal_face g 0⟩

def generatorChain {K : Type*} [Field K] (q : Gen → Kˣ) (g : Gen) : Edge rose →₀ K :=
  PathChains.chain (transport q) (generatorLoop g)

theorem edge_eq_iff (e f : Edge rose) : e = f ↔ e.src = f.src ∧ e.dst = f.dst := by
  constructor
  · intro h; cases h; exact ⟨rfl,rfl⟩
  · rintro ⟨hu,hv⟩; exact Edge.ext hu hv

theorem generatorChain_first {K : Type*} [Field K] (q : Gen → Kˣ) (g h : Gen) :
    generatorChain q g (firstEdge h) = if g = h then 1 else 0 := by
  cases g <;> cases h <;> simp [generatorChain,PathChains.chain,generatorLoop,firstEdge,
    edge,coeff,transport,unit,closingGen,b,c,index,edge_eq_iff]

/-- Three-edge columns with coefficient-correct closing orientation, on actual chains. -/
def roseMap {K : Type*} [Field K] (q : Gen → Kˣ) : (Gen → K) →ₗ[K] (Edge rose →₀ K) where
  toFun x := ∑ g, x g • generatorChain q g
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' z x := by simp [Finset.smul_sum,smul_smul]

theorem roseMap_first {K : Type*} [Field K] (q : Gen → Kˣ) (x : Gen → K) (h : Gen) :
    roseMap q x (firstEdge h) = x h := by
  simp [roseMap,generatorChain_first]

theorem roseMap_injective {K : Type*} [Field K] (q : Gen → Kˣ) : Function.Injective (roseMap q) := by
  intro x y he
  funext g
  exact (roseMap_first q x g).symm.trans ((congrArg (fun z : Edge rose →₀ K => z (firstEdge g)) he).trans (roseMap_first q y g))

theorem roseMap_single {K : Type*} [Field K] (q : Gen → Kˣ) (g : Gen) :
    roseMap q (Pi.single g 1) = generatorChain q g := by
  simp [roseMap,Pi.single_apply]

theorem complexDerivative_of (g : Gen) : complexDerivative (FreeGroup.of g) = Pi.single g 1 := by
  funext h
  by_cases hh : h = g <;> simp [complexDerivative,derivative_of,basis,hh]

theorem letter_value (l : Letter) : value originalTransport (letterPath l) =
    ComplexCharacter.character (quotientMap (freeLetter l)) := by
  have hh := DFunLike.congr_fun original_character_agreement (freeLetter l)
  change holonomy originalTransport root (evalLoops (freeLetter l)) = _ at hh
  exact (congrArg (holonomy originalTransport root) (class_letter l)).trans hh

theorem letter_chain (l : Letter) : PathChains.chain originalTransport (letterPath l) =
    roseMap generatorUnit (complexDerivative (freeLetter l)) := by
  rcases l with ⟨g,h⟩
  cases h
  · change PathChains.chain (transport generatorUnit) (reverse (generatorLoop g)) =
      roseMap generatorUnit (complexDerivative (FreeGroup.of g)⁻¹)
    rw [StellarSubdivision.chain_reverse,generator_value,complexDerivative_inv,map_neg,map_smul,
      complexDerivative_of,roseMap_single]
    have hh : ComplexCharacter.rho (quotientMap ((FreeGroup.of g : F)⁻¹)) = ((generatorUnit g)⁻¹ : ℂ) := by
      rw [← ComplexCharacter.character_value,map_inv,map_inv]
      simp [generatorUnit]
    rw [hh]
    simp [generatorChain]
  · change generatorChain generatorUnit g = roseMap generatorUnit (complexDerivative (FreeGroup.of g))
    rw [complexDerivative_of,roseMap_single]

/-- Actual weighted path chains give the evaluated LEFT Fox row for every raw word. -/
theorem word_chain (w : Word) : PathChains.chain originalTransport (wordPath w) =
    roseMap generatorUnit (complexDerivative (freeWord w)) := by
  induction w with
  | nil => simp [wordPath,PathChains.chain,ComplexFox.derivative_one]
  | cons l w ih =>
    have hv : (value originalTransport (letterPath l) : ℂ) = ComplexCharacter.rho (quotientMap (freeLetter l)) :=
      congrArg (fun z : ℂˣ => (z : ℂ)) (letter_value l)
    rw [wordPath,PathChains.chain_append,letter_chain,ih,hv,freeWord_cons,complexDerivative_mul,map_add,map_smul]

/-- The degree-one rose adapter has exactly the semantic complex Fox augmentation. -/
theorem roseMap_boundary (x : Gen → ℂ) :
    boundaryOne rose (coeff originalTransport) (roseMap generatorUnit x) =
      ComplexFox.boundaryOne x • point 0 (singleton_face 0) := by
  have hg : ∀ g, boundaryOne rose (coeff originalTransport) (generatorChain generatorUnit g) =
      ((generatorUnit g : ℂ)-1) • point 0 (singleton_face 0) := by
    intro g
    have hh := PathChains.chain_boundary (transport generatorUnit) (generatorLoop g)
    rw [generator_value] at hh
    simpa only [generatorChain,originalTransport,sub_smul,one_smul] using hh
  change boundaryOne rose (coeff originalTransport) (∑ g, x g • generatorChain generatorUnit g) =
    (∑ g, x g * ((generatorUnit g : ℂ)-1)) • point 0 (singleton_face 0)
  simp only [map_sum,map_smul,hg,smul_smul,Finset.sum_smul]

/-- A hypothetical normal-generating tuple kills the character on these actual raw paths.
It does not yet supply finite relator contractions in this unfilled rose. -/
theorem tuple_word_values {k : ℕ} (v : Fin k → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) (w : Fin k → Word)
    (hrep : ∀ j, freeWord (w j) = v j) (j : Fin k) : value originalTransport (wordPath (w j)) = 1 := by
  rw [word_value,hrep]
  have hn : v j ∈ N := hv ▸ Subgroup.subset_normalClosure (Set.mem_range_self j)
  have he : quotientMap (v j) = 1 := MonoidHom.mem_ker.mp hn
  rw [he,map_one]

/-- Actual relator PATH chains; this is not the target degree-two boundary. -/
def wordChainMap {k : ℕ} (w : Fin k → Word) : (Fin k → ℂ) →ₗ[ℂ] (Edge rose →₀ ℂ) :=
  Fintype.linearCombination ℂ (fun j => PathChains.chain originalTransport (wordPath (w j)))

theorem wordChainMap_eq {k : ℕ} (v : Fin k → F) (w : Fin k → Word)
    (hrep : ∀ j, freeWord (w j) = v j) :
    wordChainMap w = (roseMap generatorUnit).comp (ComplexFox.boundaryTwo v) := by
  apply LinearMap.ext
  intro x
  simp only [wordChainMap,ComplexFox.boundaryTwo,Fintype.linearCombination_apply,
    LinearMap.comp_apply,map_sum,map_smul,word_chain,hrep]

theorem four_tuple_path_chains_independent (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) (w : Fin 4 → Word)
    (hrep : ∀ j, freeWord (w j) = v j) : Function.Injective (wordChainMap w) := by
  rw [wordChainMap_eq v w hrep]
  exact (roseMap_injective generatorUnit).comp (ComplexFox.boundaryTwo_injective v hv)

theorem four_tuple_words_nonempty (v : Fin 4 → F)
    (hv : Subgroup.normalClosure (Set.range v) = N) (w : Fin 4 → Word)
    (hrep : ∀ j, freeWord (w j) = v j) (j : Fin 4) : w j ≠ [] := by
  intro he
  have hn := (ComplexFox.four_normal_generator_rows_independent v hv).ne_zero j
  apply hn
  rw [← hrep j,he,freeWord_nil]
  exact ComplexFox.derivative_one

/-- Reads the inverse-prefix coefficient in the literal reversed rose path. -/
theorem negative_first {K : Type*} [Field K] (q : Gen → Kˣ) (g : Gen) :
    PathChains.chain (transport q) (letterPath (neg g)) (firstEdge g) = -((q g)⁻¹ : K) := by
  change PathChains.chain (transport q) (reverse (generatorLoop g)) (firstEdge g) = _
  rw [StellarSubdivision.chain_reverse,generator_value]
  have hc : PathChains.chain (transport q) (generatorLoop g) (firstEdge g) = 1 := by
    simpa [generatorChain] using generatorChain_first q g g
  simp [hc]

/-- Scalar character agreement cannot stand in for attaching relator triangles. -/
theorem unfilled_rose_square_moves_rejected :
    ¬ Nonempty (Moves (append (generatorLoop .x1) (generatorLoop .x1)) (.refl 0 (singleton_face 0))) := by
  rintro ⟨m⟩
  have hd : value originalTransport (generatorLoop .x1) ≠ 1 := by
    intro he
    have hh := congrArg (fun z : ℂˣ => (z : ℂ)) he
    rw [x1_detected] at hh
    norm_num at hh
  apply LocalTraceUpdate.target_square_forces_noninjective rose originalTransport (generatorLoop .x1) m hd
  intro x y _
  exact Subsingleton.elim x y

theorem erased_closing_transport_rejected :
    value (PathChains.trivialTransport (K := ℂ) rose) (generatorLoop .x1) ≠
      value originalTransport (generatorLoop .x1) := by
  intro he
  have ht : value (PathChains.trivialTransport (K := ℂ) rose) (generatorLoop .x1) = 1 :=
    by simp [PathChains.trivialTransport,gaugeTransport,generatorLoop,value]
  have hh : (1 : ℂ) = -1 :=
    (congrArg (fun z : ℂˣ => (z : ℂ)) ht).symm.trans
      ((congrArg (fun z : ℂˣ => (z : ℂ)) he).trans x1_detected)
  norm_num at hh

theorem filled_generator_triangle_rejected (g : Gen) : ({0,b g,c g} : Finset Ambient) ∉ rose := by
  intro ht
  have hh := dimension_at_most_one _ ht
  cases g <;> norm_num [b,c,index] at hh

theorem raw_cancellation_length_rejected :
    freeWord [pos .x1,neg .x1] = 1 ∧ PolygonSource.length (wordPath [pos .x1,neg .x1]) ≠ 0 := by
  constructor
  · simp [freeWord,freeLetter,pos,neg]
  · rw [word_length]; decide

theorem missing_negative_prefix_transport_rejected :
    PathChains.chain (transport (fun _ : Gen => Units.mk0 (2 : ℚ) (by decide)))
      (letterPath (neg .x1)) (firstEdge .x1) ≠ -(1 : ℚ) := by
  rw [negative_first]
  norm_num

theorem incorrect_active_count_rejected : Nat.card (Vertex rose) ≠ 6 := by rw [active_vertex_count]; decide

/-- Empty arbitrary tuples do not have independent path chains without normal generation. -/
theorem omitted_normal_generation_rejected :
    ¬ Function.Injective (wordChainMap (fun _ : Fin 1 => ([] : Word))) := by
  intro hi
  have he : wordChainMap (fun _ : Fin 1 => ([] : Word)) (fun _ => 0) =
      wordChainMap (fun _ : Fin 1 => ([] : Word)) (fun _ => 1) := by
    simp [wordChainMap,Fintype.linearCombination_apply,wordPath,PathChains.chain]
  have hh := congrArg (fun f : Fin 1 → ℂ => f 0) (hi he)
  norm_num at hh

end D2RelationGap.PresentationRose
