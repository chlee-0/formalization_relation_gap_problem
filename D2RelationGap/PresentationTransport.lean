import D2RelationGap.PresentationCells

/-!
Original field-unit transport on the SAME actual privately tagged target.
Credit: OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
Finite relator Moves, degree-two Fox comparisons and geometric adequacy remain open.
-/
noncomputable section
namespace D2RelationGap.PresentationTransport
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops
open PresentationCells
variable {k : ℕ} (w : Fin k → Word) {K : Type*} [Field K]

/-- Literal initial path products; no word reduction or potential is chosen. -/
def pathPrefix {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) {u v : V} : Path A u v → ℕ → Kˣ
  | .refl _ _,_ => 1
  | .cons _ _,0 => 1
  | @Path.cons _ _ _ u v _ _ p,n+1 => tau.unit u v * pathPrefix tau p n

theorem prefix_zero {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) {u v : V} (p : Path A u v) : pathPrefix tau p 0 = 1 := by
  cases p <;> rfl

theorem prefix_end {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) {u v : V} (p : Path A u v) :
    pathPrefix tau p (PolygonSource.length p) = value tau p := by
  induction p with
  | refl => rfl
  | cons h p ih => simp only [pathPrefix,PolygonSource.length,value,ih]

theorem prefix_step {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) A) {u v : V} (p : Path A u v) (n : ℕ) (hn : n < PolygonSource.length p) :
    pathPrefix tau p (n+1) = pathPrefix tau p n * tau.unit (PolygonSource.node p n) (PolygonSource.node p (n+1)) := by
  induction p generalizing n with
  | refl => simp only [PolygonSource.length] at hn; omega
  | cons h p ih =>
    cases n with
    | zero => simp [pathPrefix,PolygonSource.node,PolygonSource.node_zero,prefix_zero]
    | succ n =>
      have hh : n < PolygonSource.length p := by simp only [PolygonSource.length] at hn; omega
      simpa only [pathPrefix,PolygonSource.node,mul_assoc] using congrArg (fun x => tau.unit _ _ * x) (ih n hh)

def prefixUnit (q : Gen → Kˣ) (j : Fin k) (i : ℕ) : Kˣ :=
  pathPrefix (PresentationRose.transport q) (PresentationRose.wordPath (w j)) i

def ell (q : Gen → Kˣ) {j : Fin k} (i : Position w j) : Kˣ :=
  PresentationRose.unit q (bottom w j i.val) (bottom w j (next w i).val)

theorem prefix_next (q : Gen → Kˣ)
    (hk : ∀ j, value (PresentationRose.transport q) (PresentationRose.wordPath (w j)) = 1)
    {j : Fin k} (i : Position w j) : prefixUnit w q j (next w i).val = prefixUnit w q j i.val * ell w q i := by
  have hs := prefix_step (PresentationRose.transport q) (PresentationRose.wordPath (w j)) i.val
    (by rw [PresentationRose.word_length]; exact i.isLt)
  change prefixUnit w q j (i.val+1) = prefixUnit w q j i.val *
    PresentationRose.unit q (bottom w j i.val) (bottom w j (i.val+1)) at hs
  rw [← bottom_next w i] at hs
  unfold next
  split_ifs with h
  · exact hs
  · have hn : i.val+1 = 3*(w j).length := by have hh := i.isLt; omega
    have hend : prefixUnit w q j (i.val+1) = 1 := by
      rw [hn,← PresentationRose.word_length]
      exact (prefix_end _ _).trans (hk j)
    have hz : prefixUnit w q j 0 = 1 := prefix_zero _ _
    exact hz.trans (hend.symm.trans hs)

theorem taggedTop_injective : Function.Injective (fun c : CollarIndex w => top c.1 c.2.val) := by
  rintro ⟨j,i⟩ ⟨l,m⟩ h
  obtain ⟨hj,hi⟩ := (top_eq_iff j l _ _).mp h
  subst l
  have hh : i = m := Fin.ext hi
  subst m
  rfl

def topIndex (x : Ambient) : Option (CollarIndex w) :=
  if h : ∃ c : CollarIndex w, top c.1 c.2.val = x then some h.choose else none

def centerIndex (_w : Fin k → Word) (x : Ambient) : Option (Fin k) :=
  if h : ∃ j : Fin k, center j = x then some h.choose else none

theorem topIndex_top {j : Fin k} (i : Position w j) : topIndex w (top j i.val) = some ⟨j,i⟩ := by
  unfold topIndex
  split_ifs with h
  · congr 1
    exact taggedTop_injective w h.choose_spec
  · exact (h ⟨⟨j,i⟩,rfl⟩).elim

theorem topIndex_center (j : Fin k) : topIndex w (center j) = none := by
  unfold topIndex
  split_ifs with h
  · obtain ⟨⟨l,i⟩,hi⟩ := h
    exact (top_ne_center l j i.val hi).elim
  · rfl

theorem topIndex_base (v : PresentationRose.Ambient) : topIndex w (base v) = none := by
  unfold topIndex
  split_ifs with h
  · obtain ⟨⟨j,i⟩,hi⟩ := h
    exact (top_ne_base j i.val v hi).elim
  · rfl

theorem center_injective : Function.Injective (center (k := k)) := by
  intro j l he
  have hh := congrArg (fun x : Ambient => x.1) he
  exact Fin.ext (by simpa [center] using hh)

theorem centerIndex_center (j : Fin k) : centerIndex w (center j) = some j := by
  unfold centerIndex
  split_ifs with h
  · congr 1
    exact center_injective h.choose_spec
  · exact (h ⟨j,rfl⟩).elim

theorem centerIndex_top (j : Fin k) (i : ℕ) : centerIndex w (top j i) = none := by
  unfold centerIndex
  split_ifs with h
  · obtain ⟨l,hl⟩ := h
    exact (center_ne_top l j i hl).elim
  · rfl

theorem centerIndex_base (v : PresentationRose.Ambient) : centerIndex w (base v) = none := by
  unfold centerIndex
  split_ifs with h
  · obtain ⟨j,hj⟩ := h
    exact (base_ne_center v j hj.symm).elim
  · rfl

theorem topIndex_sphere (j : EmptyIndex w) (i : ℕ) : topIndex w (top j.val i) = none := by
  unfold topIndex
  split_ifs with h
  · obtain ⟨⟨l,m⟩,hm⟩ := h
    have hj : l = j.val := ((top_eq_iff l j.val _ _).mp hm).1
    exact (position_nonempty w m (hj ▸ j.property)).elim
  · rfl

/-- Centers and sphere vertices have label zero; valid top vertices retain bottom labels. -/
def label (x : Ambient) : PresentationRose.Ambient :=
  match topIndex w x with
  | some c => bottom w c.1 c.2.val
  | none => if h : x.1 = 0 ∧ x.2 < 11 then ⟨x.2,h.2⟩ else 0

theorem label_base (v : PresentationRose.Ambient) : label w (base v) = v := by
  simp only [label,topIndex_base]
  have h : (base v).1 = 0 ∧ (base v).2 < 11 := ⟨rfl,v.isLt⟩
  rw [dite_eq_left h]
  rfl

theorem label_top {j : Fin k} (i : Position w j) : label w (top j i.val) = bottom w j i.val := by
  simp only [label,topIndex_top]

theorem label_center (j : Fin k) : label w (center j) = 0 := by
  simp only [label,topIndex_center]
  simp [center]

theorem label_sphere (j : EmptyIndex w) (i : ℕ) : label w (top j.val i) = 0 := by
  simp only [label,topIndex_sphere]
  simp [top]

/-- Only actual radial edges override the old rose units. Off-face values carry no meaning. -/
def radial (q : Gen → Kˣ) (u v : Ambient) : Option Kˣ :=
  match centerIndex w u, topIndex w v with
  | some j, some c => if j = c.1 then some (prefixUnit w q c.1 c.2.val) else none
  | _,_ => none

def unit (q : Gen → Kˣ) (u v : Ambient) : Kˣ :=
  match radial w q u v with
  | some z => z
  | none => match radial w q v u with
    | some z => z⁻¹
    | none => PresentationRose.unit q (label w u) (label w v)

theorem unit_noncenter (q : Gen → Kˣ) (u v : Ambient)
    (hu : centerIndex w u = none) (hv : centerIndex w v = none) :
    unit w q u v = PresentationRose.unit q (label w u) (label w v) := by
  simp only [unit,radial,hu,hv]

theorem unit_base (q : Gen → Kˣ) (u v : PresentationRose.Ambient) :
    unit w q (base u) (base v) = PresentationRose.unit q u v := by
  rw [unit_noncenter w q _ _ (centerIndex_base w u) (centerIndex_base w v),label_base,label_base]

theorem unit_top_top (q : Gen → Kˣ) {j l : Fin k} (i : Position w j) (m : Position w l) :
    unit w q (top j i.val) (top l m.val) = PresentationRose.unit q (bottom w j i.val) (bottom w l m.val) := by
  rw [unit_noncenter w q _ _ (centerIndex_top w j _) (centerIndex_top w l _),label_top,label_top]

theorem unit_center_center (q : Gen → Kˣ) (j : Fin k) : unit w q (center j) (center j) = 1 := by
  simp [unit,radial,topIndex_center,label_center,PresentationRose.unit,PresentationRose.closingGen]

theorem unit_center_top (q : Gen → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (center j) (top j i.val) = prefixUnit w q j i.val := by
  simp [unit,radial,centerIndex_center,topIndex_top]

theorem unit_top_center (q : Gen → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (top j i.val) (center j) = (prefixUnit w q j i.val)⁻¹ := by
  simp [unit,radial,centerIndex_top,centerIndex_center,topIndex_top]


theorem rose_diagonal (q : Gen → Kˣ) (u : PresentationRose.Ambient) : PresentationRose.unit q u u = 1 :=
  diagonal_unit (PresentationRose.transport q) u (PresentationRose.singleton_face u)

theorem rose_reverse (q : Gen → Kˣ) (u v : PresentationRose.Ambient)
    (h : ({u,v} : Finset PresentationRose.Ambient) ∈ PresentationRose.rose) :
    PresentationRose.unit q v u = (PresentationRose.unit q u v)⁻¹ :=
  unit_reverse (PresentationRose.transport q) u v h

/-- Nine explicit pair values imply flatness on all repeated/reordered triples. -/
theorem flat_of_pair_values (f : Ambient → Ambient → Kˣ) (a b c : Ambient) (p r : Kˣ)
    (haa : f a a = 1) (hbb : f b b = 1) (hcc : f c c = 1)
    (hab : f a b = p) (hba : f b a = p⁻¹) (hac : f a c = r) (hca : f c a = r⁻¹)
    (hbc : f b c = p⁻¹*r) (hcb : f c b = r⁻¹*p)
    (u v z : Ambient) (hu : u ∈ ({a,b,c} : Finset Ambient))
    (hv : v ∈ ({a,b,c} : Finset Ambient)) (hz : z ∈ ({a,b,c} : Finset Ambient)) :
    f u v * f v z = f u z := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv hz
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl
  all_goals simp [haa,hbb,hcc,hab,hba,hac,hca,hbc,hcb,mul_assoc]

theorem cap_flat (q : Gen → Kˣ)
    (hk : ∀ j, value (PresentationRose.transport q) (PresentationRose.wordPath (w j)) = 1)
    {j : Fin k} (i : Position w j) (u v z : Ambient)
    (hu : u ∈ cap w i) (hv : v ∈ cap w i) (hz : z ∈ cap w i) :
    unit w q u v * unit w q v z = unit w q u z := by
  apply flat_of_pair_values (unit w q) (center j) (top j i.val) (top j (next w i).val)
    (prefixUnit w q j i.val) (prefixUnit w q j (next w i).val)
  · exact unit_center_center w q j
  · rw [unit_top_top]; exact rose_diagonal q _
  · rw [unit_top_top]; exact rose_diagonal q _
  · exact unit_center_top w q i
  · exact unit_top_center w q i
  · exact unit_center_top w q (next w i)
  · exact unit_top_center w q (next w i)
  · rw [unit_top_top]
    change ell w q i = (prefixUnit w q j i.val)⁻¹ * prefixUnit w q j (next w i).val
    rw [prefix_next w q hk]
    simp
  · rw [unit_top_top,rose_reverse q _ _ (bottom_edge w i)]
    change (ell w q i)⁻¹ = (prefixUnit w q j (next w i).val)⁻¹ * prefixUnit w q j i.val
    rw [prefix_next w q hk]
    simp [mul_inv_rev,mul_assoc]
  · exact hu
  · exact hv
  · exact hz

/-- Flatness outside radial faces is inherited literally from the actual rose. -/
theorem noncenter_flat (q : Gen → Kˣ) (s : Finset Ambient)
    (hn : ∀ x ∈ s, centerIndex w x = none)
    (hl : s.image (label w) ∈ PresentationRose.rose)
    (u v z : Ambient) (hu : u ∈ s) (hv : v ∈ s) (hz : z ∈ s) :
    unit w q u v * unit w q v z = unit w q u z := by
  rw [unit_noncenter w q _ _ (hn _ hu) (hn _ hv),
    unit_noncenter w q _ _ (hn _ hv) (hn _ hz),unit_noncenter w q _ _ (hn _ hu) (hn _ hz)]
  apply PresentationRose.unit_flat q
  apply (PresentationRose.rose.isRelLowerSet_faces hl).2 _ (Finset.insert_nonempty _ _)
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
  · exact Finset.mem_image.mpr ⟨v,hv,rfl⟩
  · exact Finset.mem_image.mpr ⟨z,hz,rfl⟩

theorem upper_noncenter {j : Fin k} (i : Position w j) (x : Ambient) (hx : x ∈ upper w i) : centerIndex w x = none := by
  simp only [upper,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact centerIndex_top w _ _
  · exact centerIndex_top w _ _
  · exact centerIndex_base w _
theorem wall_noncenter {j : Fin k} (i : Position w j) (x : Ambient) (hx : x ∈ wall w i) : centerIndex w x = none := by
  simp only [wall,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact centerIndex_top w _ _
  · exact centerIndex_base w _
  · exact centerIndex_base w _
theorem sphere_noncenter (j : EmptyIndex w) (i : Fin 4) (x : Ambient) (hx : x ∈ sphere w j i) : centerIndex w x = none := by
  fin_cases i <;> simp only [sphere,Finset.mem_insert,Finset.mem_singleton] at hx
  all_goals rcases hx with rfl | rfl | rfl
  all_goals first | exact centerIndex_top w _ _ | exact centerIndex_base w _

theorem upper_label_face {j : Fin k} (i : Position w j) : (upper w i).image (label w) ∈ PresentationRose.rose := by
  apply (PresentationRose.rose.isRelLowerSet_faces (bottom_edge w i)).2 _
    ((facet_nonempty w (.inr (.inl (0,⟨j,i⟩)))).image _)
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  change y ∈ upper w i at hy
  simp only [upper,Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> simp only [label_top,label_base] <;> simp

theorem wall_label_face {j : Fin k} (i : Position w j) : (wall w i).image (label w) ∈ PresentationRose.rose := by
  apply (PresentationRose.rose.isRelLowerSet_faces (bottom_edge w i)).2 _
    ((facet_nonempty w (.inr (.inl (1,⟨j,i⟩)))).image _)
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  change y ∈ wall w i at hy
  simp only [wall,Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> simp only [label_top,label_base] <;> simp

theorem sphere_label_face (j : EmptyIndex w) (i : Fin 4) : (sphere w j i).image (label w) ∈ PresentationRose.rose := by
  apply (PresentationRose.rose.isRelLowerSet_faces (PresentationRose.singleton_face 0)).2 _
    ((facet_nonempty w (.inr (.inr (j,i)))).image _)
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  change y ∈ sphere w j i at hy
  fin_cases i <;> simp only [sphere,Finset.mem_insert,Finset.mem_singleton] at hy
  all_goals rcases hy with rfl | rfl | rfl
  all_goals simp only [label_sphere,label_base,Finset.mem_singleton]

/-- Flatness is checked on every actual facet, including all collapsed orientations. -/
theorem unit_flat (q : Gen → Kˣ)
    (hk : ∀ j, value (PresentationRose.transport q) (PresentationRose.wordPath (w j)) = 1)
    (u v z : Ambient) (h : ({u,v,z} : Finset Ambient) ∈ target w) :
    unit w q u v * unit w q v z = unit w q u z := by
  obtain ⟨f,hf⟩ := h.2
  have hu := hf (show u ∈ ({u,v,z} : Finset Ambient) by simp)
  have hv := hf (show v ∈ ({u,v,z} : Finset Ambient) by simp)
  have hz := hf (show z ∈ ({u,v,z} : Finset Ambient) by simp)
  rcases f with ⟨g,i⟩ | (⟨t,_j,i⟩ | ⟨j,i⟩)
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
    rw [unit_base,unit_base,unit_base]
    apply PresentationRose.unit_flat q
    apply (PresentationRose.rose.isRelLowerSet_faces (PresentationRose.petal_face g i)).2 _ (Finset.insert_nonempty _ _)
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  · fin_cases t
    · exact noncenter_flat w q _ (upper_noncenter w i) (upper_label_face w i) u v z hu hv hz
    · exact noncenter_flat w q _ (wall_noncenter w i) (wall_label_face w i) u v z hu hv hz
    · exact cap_flat w q hk i u v z hu hv hz
  · exact noncenter_flat w q _ (sphere_noncenter w j i) (sphere_label_face w j i) u v z hu hv hz

def transport (q : Gen → Kˣ)
    (hk : ∀ j, value (PresentationRose.transport q) (PresentationRose.wordPath (w j)) = 1) : Transport (K := K) (target w) :=
  ⟨unit w q,unit_flat w q hk⟩


theorem vertical_unit (q : Gen → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (top j i.val) (base (bottom w j i.val)) = 1 := by
  rw [unit_noncenter w q _ _ (centerIndex_top w _ _) (centerIndex_base w _),label_top,label_base]
  exact rose_diagonal q _

theorem diagonal_unit (q : Gen → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (top j i.val) (base (bottom w j (next w i).val)) = ell w q i := by
  rw [unit_noncenter w q _ _ (centerIndex_top w _ _) (centerIndex_base w _),label_top,label_base]
  rfl

theorem top_edge_unit (q : Gen → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (top j i.val) (top j (next w i).val) = ell w q i := unit_top_top w q i (next w i)

theorem sphere_label_zero (j : EmptyIndex w) (i : Fin 4) (x : Ambient) (hx : x ∈ sphere w j i) : label w x = 0 := by
  fin_cases i <;> simp only [sphere,Finset.mem_insert,Finset.mem_singleton] at hx
  all_goals rcases hx with rfl | rfl | rfl
  all_goals first | exact label_sphere w j _ | exact label_base w 0

theorem sphere_unit_one (q : Gen → Kˣ) (j : EmptyIndex w) (i : Fin 4) (u v : Ambient)
    (hu : u ∈ sphere w j i) (hv : v ∈ sphere w j i) : unit w q u v = 1 := by
  rw [unit_noncenter w q _ _ (sphere_noncenter w j i _ hu) (sphere_noncenter w j i _ hv),
    sphere_label_zero w j i _ hu,sphere_label_zero w j i _ hv]
  exact rose_diagonal q 0

/-- Literal pullback, not equality under only one distinguished character. -/
theorem pullback_transport (q : Gen → Kˣ)
    (hk : ∀ j, value (PresentationRose.transport q) (PresentationRose.wordPath (w j)) = 1) :
    pullback (transport w q hk) base (baseMap w) = PresentationRose.transport q := by
  change Transport.mk _ _ = Transport.mk _ _
  congr 1
  funext u v
  exact unit_base w q u v

theorem old_path_value (q : Gen → Kˣ)
    (hk : ∀ j, value (PresentationRose.transport q) (PresentationRose.wordPath (w j)) = 1)
    {u v : PresentationRose.Ambient} (p : Path PresentationRose.rose u v) :
    value (transport w q hk) (mapPath base (baseMap w) p) = value (PresentationRose.transport q) p := by
  rw [value_mapPath,pullback_transport]

def generatorLoop (g : Gen) : Path (target w) (base 0) (base 0) :=
  mapPath base (baseMap w) (PresentationRose.generatorLoop g)

instance targetLoopGroup : Group (Loop (target w) (root w)) := loopGroup (target w) (root w)

def evalLoops : Targets.F →* Loop (target w) (root w) :=
  FreeGroup.lift (fun g => Quotient.mk _ (generatorLoop w g))

theorem generator_value (q : Gen → Kˣ)
    (hk : ∀ j, value (PresentationRose.transport q) (PresentationRose.wordPath (w j)) = 1) (g : Gen) :
    value (transport w q hk) (generatorLoop w g) = q g :=
  (old_path_value w q hk _).trans (PresentationRose.generator_value q g)

/-- The character-killing premise follows from the ACTUAL original normal kernel. -/
theorem tuple_kills (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    ∀ j, value (PresentationRose.transport PresentationRose.generatorUnit) (PresentationRose.wordPath (w j)) = 1 :=
  PresentationRose.tuple_word_values v hv w hrep

def tupleTransport (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) : Transport (K := ℂ) (target w) :=
  transport w PresentationRose.generatorUnit (tuple_kills w v hv hrep)

/-- ORIGINAL character agreement on ALL actual F, on the SAME constructed target. -/
theorem original_character_agreement (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    (holonomy (tupleTransport w v hv hrep) (root w)).comp (evalLoops w) =
      ComplexCharacter.character.comp Targets.quotientMap := by
  apply FreeGroup.ext_hom
  intro g
  change value (tupleTransport w v hv hrep) (generatorLoop w g) = PresentationRose.generatorUnit g
  exact generator_value w _ (tuple_kills w v hv hrep) g

theorem original_path_values (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j)
    {u z : PresentationRose.Ambient} (p : Path PresentationRose.rose u z) :
    value (tupleTransport w v hv hrep) (mapPath base (baseMap w) p) = value PresentationRose.originalTransport p :=
  old_path_value w _ (tuple_kills w v hv hrep) p

theorem original_x1_detected (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    ((value (tupleTransport w v hv hrep) (generatorLoop w .x1) : ℂˣ) : ℂ) = -1 := by
  have he := original_path_values w v hv hrep (PresentationRose.generatorLoop .x1)
  exact (congrArg (fun z : ℂˣ => (z : ℂ)) he).trans PresentationRose.x1_detected


def wordPath (raw : Word) : Path (target w) (base 0) (base 0) :=
  mapPath base (baseMap w) (PresentationRose.wordPath raw)

theorem evalLoops_natural : evalLoops w =
    (BasedLoops.map base (baseMap w) PresentationRose.root).comp PresentationRose.evalLoops := by
  apply FreeGroup.ext_hom
  intro g
  simp only [evalLoops,PresentationRose.evalLoops,FreeGroup.lift_apply_of]
  rfl

theorem class_word (raw : Word) :
    (Quotient.mk _ (wordPath w raw) : Loop (target w) (root w)) = evalLoops w (Targets.freeWord raw) := by
  have h := congrArg (BasedLoops.map base (baseMap w) PresentationRose.root) (PresentationRose.class_word raw)
  change (Quotient.mk _ (wordPath w raw) : Loop (target w) (root w)) =
    ((BasedLoops.map base (baseMap w) PresentationRose.root).comp PresentationRose.evalLoops) (Targets.freeWord raw) at h
  rw [← evalLoops_natural] at h
  exact h

theorem original_word_value (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) (raw : Word) :
    value (tupleTransport w v hv hrep) (wordPath w raw) =
      ComplexCharacter.character (Targets.quotientMap (Targets.freeWord raw)) :=
  (original_path_values w v hv hrep (PresentationRose.wordPath raw)).trans (PresentationRose.word_value raw)

/-- Exact sign transport witnesses prefix and wraparound errors. -/
def signUnit : Gen → ℚˣ := fun _ => Units.mk0 (-1 : ℚ) (by decide)
abbrev signWords : Fin 1 → Word := fun _ => [pos .x1,pos .x1]

theorem sign_words_killed : ∀ j, value (PresentationRose.transport signUnit) (PresentationRose.wordPath (signWords j)) = 1 := by
  intro j
  simp [PresentationRose.wordPath,PresentationRose.letterPath,pos,value_append,
    PresentationRose.generator_value,value,signUnit]
  apply Units.ext
  norm_num

theorem sign_prefix_three : prefixUnit signWords signUnit 0 3 = -1 := by
  norm_num [prefixUnit,pathPrefix,signWords,PresentationRose.wordPath,PresentationRose.letterPath,pos,
    PresentationRose.generatorLoop,append,PresentationRose.transport,PresentationRose.unit,
    PresentationRose.closingGen,PresentationRose.b,PresentationRose.c,PresentationRose.index]
  exact Units.ext rfl

theorem missing_radial_prefix_rejected : unit signWords signUnit (center (0 : Fin 1)) (top (0 : Fin 1) 3) ≠ 1 := by
  have h := unit_center_top signWords signUnit (j := 0) (⟨3,by decide⟩ : Position signWords 0)
  rw [sign_prefix_three] at h
  rw [h]
  decide

theorem missing_closing_top_transport_rejected :
    unit signWords signUnit (top (0 : Fin 1) 2) (top (0 : Fin 1) 3) ≠ 1 := by
  have h := top_edge_unit signWords signUnit (j := 0) (⟨2,by decide⟩ : Position signWords 0)
  norm_num [ell,bottom,next,signWords,PresentationRose.wordPath,PresentationRose.letterPath,pos,
    PresentationRose.generatorLoop,append,PolygonSource.node,PresentationRose.unit,
    PresentationRose.closingGen,PresentationRose.b,PresentationRose.c,PresentationRose.index,signUnit] at h
  rw [h]
  decide

/-- The LABEL alone is not a global face map; cap transport uses radial prefixes. -/
theorem copied_label_face_map_rejected : ¬ (target signWords).map (label signWords) ≤ PresentationRose.rose := by
  intro hf
  have hh := image_mem (label signWords) hf _ (cap_face signWords (j := 0) (⟨1,by decide⟩ : Position signWords 0))
  have he : (cap signWords (j := 0) (⟨1,by decide⟩ : Position signWords 0)).image (label signWords) =
      {0,PresentationRose.b .x1,PresentationRose.c .x1} := by
    change ({center (0 : Fin 1),top (0 : Fin 1) 1,top (0 : Fin 1) 2} : Finset Ambient).image (label signWords) = _
    ext x
    simp only [Finset.mem_image,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨y,hy,rfl⟩
      rcases hy with rfl | rfl | rfl
      · simp only [label_center]; simp
      · rw [label_top signWords (j := 0) (⟨1,by decide⟩ : Position signWords 0)]
        simp [bottom,PresentationRose.wordPath,PresentationRose.letterPath,pos,
          PresentationRose.generatorLoop,append,PolygonSource.node]
      · rw [label_top signWords (j := 0) (⟨2,by decide⟩ : Position signWords 0)]
        simp [bottom,PresentationRose.wordPath,PresentationRose.letterPath,pos,
          PresentationRose.generatorLoop,append,PolygonSource.node]
    · rintro (rfl | rfl | rfl)
      · exact ⟨center (0 : Fin 1),by simp, label_center signWords 0⟩
      · exact ⟨top (0 : Fin 1) 1,by simp,by rw [label_top signWords (j := 0) (⟨1,by decide⟩ : Position signWords 0)]; rfl⟩
      · exact ⟨top (0 : Fin 1) 2,by simp,by rw [label_top signWords (j := 0) (⟨2,by decide⟩ : Position signWords 0)]; rfl⟩
  rw [he] at hh
  exact PresentationRose.filled_generator_triangle_rejected .x1 hh


abbrev singleWords : Fin 1 → Word := fun _ => [pos .x1]
def twoUnit : Gen → ℚˣ := fun _ => Units.mk0 (2 : ℚ) (by decide)
abbrev inverseWords : Fin 1 → Word := fun _ => [neg .x1,pos .x1]

/-- Dropping the killed-word condition corrupts the LAST actual cap triangle. -/
theorem omitted_wraparound_killing_rejected :
    unit singleWords twoUnit (center (0 : Fin 1)) (top (0 : Fin 1) 2) *
      unit singleWords twoUnit (top (0 : Fin 1) 2) (top (0 : Fin 1) 0) ≠
      unit singleWords twoUnit (center (0 : Fin 1)) (top (0 : Fin 1) 0) := by
  have htop := top_edge_unit singleWords twoUnit (j := 0) (⟨2,by decide⟩ : Position singleWords 0)
  have hn : (next singleWords (j := 0) (⟨2,by decide⟩ : Position singleWords 0)).val = 0 := rfl
  rw [hn] at htop
  rw [unit_center_top singleWords twoUnit (j := 0) (⟨2,by decide⟩ : Position singleWords 0),
    unit_center_top singleWords twoUnit (j := 0) (⟨0,by decide⟩ : Position singleWords 0),htop]
  intro he
  have hh := congrArg (fun z : ℚˣ => (z : ℚ)) he
  norm_num [prefixUnit,pathPrefix,ell,bottom,next,PresentationRose.wordPath,PresentationRose.letterPath,
    PresentationRose.generatorLoop,append,PolygonSource.node,PresentationRose.transport,PresentationRose.unit,
    PresentationRose.closingGen,PresentationRose.b,PresentationRose.c,PresentationRose.index,pos,twoUnit] at hh

/-- A nonunitary witness sees an inverse that sign-only examples could hide. -/
theorem wrong_negative_radial_inverse_rejected :
    (unit inverseWords twoUnit (center (0 : Fin 1)) (top (0 : Fin 1) 1) : ℚ) ≠ 2 := by
  rw [unit_center_top inverseWords twoUnit (j := 0) (⟨1,by decide⟩ : Position inverseWords 0)]
  norm_num [prefixUnit,pathPrefix,PresentationRose.wordPath,PresentationRose.letterPath,neg,
    PresentationRose.generatorLoop,append,reverse,single,PresentationRose.transport,PresentationRose.unit,
    PresentationRose.closingGen,PresentationRose.b,PresentationRose.c,PresentationRose.index,twoUnit]

/-- A vertex gauge would erase the ORIGINAL detected loop on this SAME target. -/
theorem erased_original_holonomy_rejected (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    value (PathChains.trivialTransport (K := ℂ) (target w)) (generatorLoop w .x1) ≠
      value (tupleTransport w v hv hrep) (generatorLoop w .x1) := by
  have ht {u z : Ambient} (p : Path (target w) u z) :
      value (PathChains.trivialTransport (K := ℂ) (target w)) p = 1 := by
    induction p with
    | refl => rfl
    | cons h p ih =>
      rw [value,ih]
      simp [PathChains.trivialTransport,gaugeTransport]
  intro he
  have hh := congrArg (fun z : ℂˣ => (z : ℂ)) he
  rw [ht,original_x1_detected w v hv hrep] at hh
  norm_num at hh


/-- The tagged base embedding retains the ACTUAL original vertex order. -/
theorem base_order (u v : PresentationRose.Ambient) (h : u < v) : base u < base v :=
  Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl,h⟩)

def includeEdge (e : Edge PresentationRose.rose) : Edge (target w) :=
  ⟨base e.src,base e.dst,base_order _ _ e.ordered,by
    simpa using base_face w {e.src,e.dst} e.face⟩

theorem includeEdge_injective : Function.Injective (includeEdge w) := by
  intro e f he
  exact Edge.ext (base_injective (congrArg Edge.src he)) (base_injective (congrArg Edge.dst he))

def includeChains : (Edge PresentationRose.rose →₀ K) →ₗ[K] (Edge (target w) →₀ K) :=
  Finsupp.lmapDomain K K (includeEdge w)

theorem includeChains_injective : Function.Injective (includeChains (K := K) w) :=
  Finsupp.mapDomain_injective (includeEdge_injective w)

/-- Positive sorted rose edges extend with coefficient one; closing/reversal
weights have already been accounted for in the original rose chain. -/
theorem includeChains_eq_edgeMap (tau : Transport (K := K) (target w)) :
    includeChains w = edgeMap tau base (baseMap w) := by
  apply Finsupp.lhom_ext
  intro e c
  simp [includeChains,Finsupp.lmapDomain,edgeMap,edge,base_order e.src e.dst e.ordered,includeEdge]

def roseMap (q : Gen → Kˣ) : (Gen → K) →ₗ[K] (Edge (target w) →₀ K) :=
  (includeChains w).comp (PresentationRose.roseMap q)

theorem roseMap_injective (q : Gen → Kˣ) : Function.Injective (roseMap w q) :=
  (includeChains_injective w).comp (PresentationRose.roseMap_injective q)

theorem word_chain (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) (raw : Word) :
    PathChains.chain (tupleTransport w v hv hrep) (wordPath w raw) =
      roseMap w PresentationRose.generatorUnit (FoxSemantics.complexDerivative (Targets.freeWord raw)) := by
  have hn := StellarSubdivision.map_path_chain (tupleTransport w v hv hrep) base (baseMap w) (PresentationRose.wordPath raw)
  rw [show pullback (tupleTransport w v hv hrep) base (baseMap w) = PresentationRose.originalTransport from
    pullback_transport w _ (tuple_kills w v hv hrep),PresentationRose.word_chain] at hn
  rw [← includeChains_eq_edgeMap] at hn
  exact hn.symm

/-- SAME tuple: actual target path chains intertwine the semantic Fox map.
This is still not the degree-two target boundary. -/
theorem tuple_path_chain_comparison (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    Fintype.linearCombination ℂ (fun j => PathChains.chain (tupleTransport w v hv hrep) (mappedWord w j)) =
      (roseMap w PresentationRose.generatorUnit).comp (ComplexFox.boundaryTwo v) := by
  apply LinearMap.ext
  intro x
  simp only [Fintype.linearCombination_apply,LinearMap.comp_apply,ComplexFox.boundaryTwo]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show mappedWord w j = wordPath w (w j) from rfl,word_chain w v hv hrep,hrep]


/-- The actual target's degree-one boundary of J1 is the original Fox augmentation. -/
theorem roseMap_boundary (v : Fin k → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) (x : Gen → ℂ) :
    boundaryOne (target w) (coeff (tupleTransport w v hv hrep)) (roseMap w PresentationRose.generatorUnit x) =
      ComplexFox.boundaryOne x • point (base 0) (root w).property := by
  have hn := LinearMap.congr_fun (map_boundary_one (tupleTransport w v hv hrep) base (baseMap w))
    (PresentationRose.roseMap PresentationRose.generatorUnit x)
  rw [← includeChains_eq_edgeMap,show pullback (tupleTransport w v hv hrep) base (baseMap w) =
    PresentationRose.originalTransport from pullback_transport w _ (tuple_kills w v hv hrep)] at hn
  change boundaryOne (target w) (coeff (tupleTransport w v hv hrep)) (roseMap w PresentationRose.generatorUnit x) =
    vertexMap base (baseMap w) (boundaryOne PresentationRose.rose (coeff PresentationRose.originalTransport)
      (PresentationRose.roseMap PresentationRose.generatorUnit x)) at hn
  rw [PresentationRose.roseMap_boundary,map_smul] at hn
  simpa [vertexMap,Finsupp.lmapDomain,point,mapVertex] using hn

/-- These independent ACTUAL path columns still are not the target d2 columns. -/
theorem four_tuple_path_chains_independent (v : Fin 4 → Targets.F)
    (hv : Subgroup.normalClosure (Set.range v) = Targets.N) (w : Fin 4 → Word)
    (hrep : ∀ j, Targets.freeWord (w j) = v j) :
    Function.Injective (Fintype.linearCombination ℂ
      (fun j => PathChains.chain (tupleTransport w v hv hrep) (mappedWord w j))) := by
  rw [tuple_path_chain_comparison]
  exact (roseMap_injective w PresentationRose.generatorUnit).comp (ComplexFox.boundaryTwo_injective v hv)

end D2RelationGap.PresentationTransport
