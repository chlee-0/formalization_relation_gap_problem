import D2RelationGap.ArbCells
import D2RelationGap.PresentationTransport

/-!
Original-character transport on the arbitrary-rank tagged target (`ArbCells`):
literal raw-path radial prefixes, flat on every actual face. Ports
`PresentationTransport` with the arbitrary-rank rose. OpenAI, "A Counterexample to
Wall's D(2) Problem" (October 6, 2026), openai/math
adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/.
-/
noncomputable section
namespace D2RelationGap.ArbTransport
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops
open ArbCells
open PresentationTransport (pathPrefix prefix_zero prefix_end prefix_step)
variable {m k : ℕ} (w : Fin k → ArbRose.AWord m) {K : Type*} [Field K]

def prefixUnit (q : Fin m → Kˣ) (j : Fin k) (i : ℕ) : Kˣ :=
  pathPrefix (ArbRose.transport q) (ArbRose.wordPath (w j)) i

def ell (q : Fin m → Kˣ) {j : Fin k} (i : Position w j) : Kˣ :=
  ArbRose.unit q (bottom w j i.val) (bottom w j (next w i).val)

theorem prefix_next (q : Fin m → Kˣ)
    (hk : ∀ j, value (ArbRose.transport q) (ArbRose.wordPath (w j)) = 1)
    {j : Fin k} (i : Position w j) : prefixUnit w q j (next w i).val = prefixUnit w q j i.val * ell w q i := by
  have hs := prefix_step (ArbRose.transport q) (ArbRose.wordPath (w j)) i.val
    (by rw [ArbRose.word_length]; exact i.isLt)
  change prefixUnit w q j (i.val+1) = prefixUnit w q j i.val *
    ArbRose.unit q (bottom w j i.val) (bottom w j (i.val+1)) at hs
  rw [← bottom_next w i] at hs
  unfold next
  split_ifs with h
  · exact hs
  · have hn : i.val+1 = 3*(w j).length := by have hh := i.isLt; omega
    have hend : prefixUnit w q j (i.val+1) = 1 := by
      rw [hn,← ArbRose.word_length]
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

def centerIndex (_w : Fin k → ArbRose.AWord m) (x : Ambient) : Option (Fin k) :=
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

theorem topIndex_base (v : ℕ) : topIndex w (base v) = none := by
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

theorem centerIndex_base (v : ℕ) : centerIndex w (base v) = none := by
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
def label (x : Ambient) : ℕ :=
  match topIndex w x with
  | some c => bottom w c.1 c.2.val
  | none => if x.1 = 0 then x.2 else 0

theorem label_base (v : ℕ) : label w (base v) = v := by
  simp only [label,topIndex_base]
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
def radial (q : Fin m → Kˣ) (u v : Ambient) : Option Kˣ :=
  match centerIndex w u, topIndex w v with
  | some j, some c => if j = c.1 then some (prefixUnit w q c.1 c.2.val) else none
  | _,_ => none

def unit (q : Fin m → Kˣ) (u v : Ambient) : Kˣ :=
  match radial w q u v with
  | some z => z
  | none => match radial w q v u with
    | some z => z⁻¹
    | none => ArbRose.unit q (label w u) (label w v)

theorem unit_noncenter (q : Fin m → Kˣ) (u v : Ambient)
    (hu : centerIndex w u = none) (hv : centerIndex w v = none) :
    unit w q u v = ArbRose.unit q (label w u) (label w v) := by
  simp only [unit,radial,hu,hv]

theorem unit_base (q : Fin m → Kˣ) (u v : ℕ) :
    unit w q (base u) (base v) = ArbRose.unit q u v := by
  rw [unit_noncenter w q _ _ (centerIndex_base w u) (centerIndex_base w v),label_base,label_base]

theorem unit_top_top (q : Fin m → Kˣ) {j l : Fin k} (i : Position w j) (m : Position w l) :
    unit w q (top j i.val) (top l m.val) = ArbRose.unit q (bottom w j i.val) (bottom w l m.val) := by
  rw [unit_noncenter w q _ _ (centerIndex_top w j _) (centerIndex_top w l _),label_top,label_top]

theorem unit_center_center (q : Fin m → Kˣ) (j : Fin k) : unit w q (center j) (center j) = 1 := by
  simp [unit,radial,topIndex_center,label_center,ArbRose.unit_self]

theorem unit_center_top (q : Fin m → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (center j) (top j i.val) = prefixUnit w q j i.val := by
  simp [unit,radial,centerIndex_center,topIndex_top]

theorem unit_top_center (q : Fin m → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (top j i.val) (center j) = (prefixUnit w q j i.val)⁻¹ := by
  simp [unit,radial,centerIndex_top,centerIndex_center,topIndex_top]


theorem rose_diagonal (q : Fin m → Kˣ) (u : ℕ) : ArbRose.unit q u u = 1 :=
  ArbRose.unit_self q u

theorem rose_reverse (q : Fin m → Kˣ) (u v : ℕ)
    (_h : ({u,v} : Finset ℕ) ∈ ArbRose.rose m) :
    ArbRose.unit q v u = (ArbRose.unit q u v)⁻¹ :=
  eq_inv_of_mul_eq_one_left (ArbRose.unit_swap q v u)

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

theorem cap_flat (q : Fin m → Kˣ)
    (hk : ∀ j, value (ArbRose.transport q) (ArbRose.wordPath (w j)) = 1)
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
theorem noncenter_flat (q : Fin m → Kˣ) (s : Finset Ambient)
    (hn : ∀ x ∈ s, centerIndex w x = none)
    (hl : s.image (label w) ∈ ArbRose.rose m)
    (u v z : Ambient) (hu : u ∈ s) (hv : v ∈ s) (hz : z ∈ s) :
    unit w q u v * unit w q v z = unit w q u z := by
  rw [unit_noncenter w q _ _ (hn _ hu) (hn _ hv),
    unit_noncenter w q _ _ (hn _ hv) (hn _ hz),unit_noncenter w q _ _ (hn _ hu) (hn _ hz)]
  apply ArbRose.unit_flat q
  apply ((ArbRose.rose m).isRelLowerSet_faces hl).2 _ (Finset.insert_nonempty _ _)
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

theorem upper_label_face {j : Fin k} (i : Position w j) : (upper w i).image (label w) ∈ ArbRose.rose m := by
  apply ((ArbRose.rose m).isRelLowerSet_faces (bottom_edge w i)).2 _
    ((cell_face w (.inl (0,⟨j,i⟩))).1.image _)
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  change y ∈ upper w i at hy
  simp only [upper,Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> simp only [label_top,label_base] <;> simp

theorem wall_label_face {j : Fin k} (i : Position w j) : (wall w i).image (label w) ∈ ArbRose.rose m := by
  apply ((ArbRose.rose m).isRelLowerSet_faces (bottom_edge w i)).2 _
    ((cell_face w (.inl (1,⟨j,i⟩))).1.image _)
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  change y ∈ wall w i at hy
  simp only [wall,Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> simp only [label_top,label_base] <;> simp

theorem sphere_label_face (j : EmptyIndex w) (i : Fin 4) : (sphere w j i).image (label w) ∈ ArbRose.rose m := by
  apply ((ArbRose.rose m).isRelLowerSet_faces (ArbRose.root_face m)).2 _
    ((cell_face w (.inr (j,i))).1.image _)
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  change y ∈ sphere w j i at hy
  fin_cases i <;> simp only [sphere,Finset.mem_insert,Finset.mem_singleton] at hy
  all_goals rcases hy with rfl | rfl | rfl
  all_goals simp only [label_sphere,label_base,Finset.mem_singleton]

/-- Flatness is checked on every actual facet, including all collapsed orientations. -/
theorem unit_flat (q : Fin m → Kˣ)
    (hk : ∀ j, value (ArbRose.transport q) (ArbRose.wordPath (w j)) = 1)
    (u v z : Ambient) (h : ({u,v,z} : Finset Ambient) ∈ target w) :
    unit w q u v * unit w q v z = unit w q u z := by
  rcases h.2 with ⟨r,hr,hf⟩ | ⟨f,hf⟩
  · have hu := hf (show u ∈ ({u,v,z} : Finset Ambient) by simp)
    have hv := hf (show v ∈ ({u,v,z} : Finset Ambient) by simp)
    have hz := hf (show z ∈ ({u,v,z} : Finset Ambient) by simp)
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
    rw [unit_base,unit_base,unit_base]
    apply ArbRose.unit_flat q
    apply ((ArbRose.rose m).isRelLowerSet_faces hr).2 _ (Finset.insert_nonempty _ _)
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  · have hu := hf (show u ∈ ({u,v,z} : Finset Ambient) by simp)
    have hv := hf (show v ∈ ({u,v,z} : Finset Ambient) by simp)
    have hz := hf (show z ∈ ({u,v,z} : Finset Ambient) by simp)
    rcases f with ⟨t,_j,i⟩ | ⟨j,i⟩
    · fin_cases t
      · exact noncenter_flat w q _ (upper_noncenter w i) (upper_label_face w i) u v z hu hv hz
      · exact noncenter_flat w q _ (wall_noncenter w i) (wall_label_face w i) u v z hu hv hz
      · exact cap_flat w q hk i u v z hu hv hz
    · exact noncenter_flat w q _ (sphere_noncenter w j i) (sphere_label_face w j i) u v z hu hv hz

def transport (q : Fin m → Kˣ)
    (hk : ∀ j, value (ArbRose.transport q) (ArbRose.wordPath (w j)) = 1) : Transport (K := K) (target w) :=
  ⟨unit w q,unit_flat w q hk⟩


theorem vertical_unit (q : Fin m → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (top j i.val) (base (bottom w j i.val)) = 1 := by
  rw [unit_noncenter w q _ _ (centerIndex_top w _ _) (centerIndex_base w _),label_top,label_base]
  exact rose_diagonal q _

theorem diagonal_unit (q : Fin m → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (top j i.val) (base (bottom w j (next w i).val)) = ell w q i := by
  rw [unit_noncenter w q _ _ (centerIndex_top w _ _) (centerIndex_base w _),label_top,label_base]
  rfl

theorem top_edge_unit (q : Fin m → Kˣ) {j : Fin k} (i : Position w j) :
    unit w q (top j i.val) (top j (next w i).val) = ell w q i := unit_top_top w q i (next w i)

theorem sphere_label_zero (j : EmptyIndex w) (i : Fin 4) (x : Ambient) (hx : x ∈ sphere w j i) : label w x = 0 := by
  fin_cases i <;> simp only [sphere,Finset.mem_insert,Finset.mem_singleton] at hx
  all_goals rcases hx with rfl | rfl | rfl
  all_goals first | exact label_sphere w j _ | exact label_base w 0

theorem sphere_unit_one (q : Fin m → Kˣ) (j : EmptyIndex w) (i : Fin 4) (u v : Ambient)
    (hu : u ∈ sphere w j i) (hv : v ∈ sphere w j i) : unit w q u v = 1 := by
  rw [unit_noncenter w q _ _ (sphere_noncenter w j i _ hu) (sphere_noncenter w j i _ hv),
    sphere_label_zero w j i _ hu,sphere_label_zero w j i _ hv]
  exact rose_diagonal q 0

/-- Literal pullback, not equality under only one distinguished character. -/
theorem pullback_transport (q : Fin m → Kˣ)
    (hk : ∀ j, value (ArbRose.transport q) (ArbRose.wordPath (w j)) = 1) :
    pullback (transport w q hk) base (baseMap w) = ArbRose.transport q := by
  change Transport.mk _ _ = Transport.mk _ _
  congr 1
  funext u v
  exact unit_base w q u v

theorem old_path_value (q : Fin m → Kˣ)
    (hk : ∀ j, value (ArbRose.transport q) (ArbRose.wordPath (w j)) = 1)
    {u v : ℕ} (p : Path (ArbRose.rose m) u v) :
    value (transport w q hk) (mapPath base (baseMap w) p) = value (ArbRose.transport q) p := by
  rw [value_mapPath,pullback_transport]

def wordPath (raw : ArbRose.AWord m) : Path (target w) (base 0) (base 0) :=
  mapPath base (baseMap w) (ArbRose.wordPath raw)

instance targetLoopGroup : Group (Loop (target w) (root w)) := loopGroup (target w) (root w)

def evalLoops : FreeGroup (Fin m) →* Loop (target w) (root w) :=
  (BasedLoops.map base (baseMap w) (ArbRose.root m)).comp ArbRose.evalLoops

theorem class_word (raw : ArbRose.AWord m) :
    (Quotient.mk _ (wordPath w raw) : Loop (target w) (root w)) = evalLoops w (ArbRose.freeWord raw) := by
  have h := congrArg (BasedLoops.map base (baseMap w) (ArbRose.root m)) (ArbRose.class_word raw)
  exact h

/-- The tagged base embedding retains the ACTUAL original vertex order. -/
theorem base_order (u v : ℕ) (h : u < v) : base u < base v :=
  Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl,h⟩)

def includeEdge (e : Edge (ArbRose.rose m)) : Edge (target w) :=
  ⟨base e.src,base e.dst,base_order _ _ e.ordered,by
    simpa using base_face w {e.src,e.dst} e.face⟩

theorem includeEdge_injective : Function.Injective (includeEdge w) := by
  intro e f he
  exact Edge.ext (base_injective (congrArg Edge.src he)) (base_injective (congrArg Edge.dst he))

def includeChains : (Edge (ArbRose.rose m) →₀ K) →ₗ[K] (Edge (target w) →₀ K) :=
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

def roseMap (q : Fin m → Kˣ) : (Fin m → K) →ₗ[K] (Edge (target w) →₀ K) :=
  (includeChains w).comp (ArbRose.roseMap q)

theorem roseMap_injective (q : Fin m → Kˣ) : Function.Injective (roseMap w q) :=
  (includeChains_injective w).comp (ArbRose.roseMap_injective q)


theorem word_chain (χ : FreeGroup (Fin m) →* K)
    (hk : ∀ j, value (ArbRose.transport (fun i => GenericFox.unitsChar χ (FreeGroup.of i)))
      (ArbRose.wordPath (w j)) = 1) (raw : ArbRose.AWord m) :
    PathChains.chain (transport w _ hk) (wordPath w raw) =
      roseMap w (fun i => GenericFox.unitsChar χ (FreeGroup.of i)) (GenericFox.D χ (ArbRose.freeWord raw)) := by
  have hn := StellarSubdivision.map_path_chain (transport w _ hk) base (baseMap w) (ArbRose.wordPath raw)
  rw [pullback_transport w _ hk, ArbRose.word_chain] at hn
  rw [← includeChains_eq_edgeMap] at hn
  exact hn.symm

end D2RelationGap.ArbTransport
