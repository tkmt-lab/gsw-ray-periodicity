import Formal.GCPrimitiveStarts

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive GCChallengeBridge
variable {k l : ℤ}

def mapTriangle {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (E : G ≃g H) (t : R002.OrderedTriangle G) : R002.OrderedTriangle H :=
  ⟨E t.a,E t.b,E t.c,E.map_adj_iff.mpr t.ab,E.map_adj_iff.mpr t.bc,E.map_adj_iff.mpr t.ca⟩

def mapStart (E : graph k l ≃g graph k l) (s : Start k l) : Start k l :=
  ⟨mapTriangle E s.val,by simpa only [mapTriangle,iso_degree] using s.property⟩

theorem rotate_parent (r : Rotation) (d : Dart) :
    rotateVertex (k:=k) (l:=l) r (parent d)=parent (rotateDart r d) := by
  simp only [parent,rotateVertex_vertex,rotateRaw_corner]

theorem rotate_fan (hkl : l<k) (hl : 0<l) (r : Rotation) (d : Dart) :
    rotateVertex r (fan hkl hl d)=fan hkl hl (rotateDart r d) := by
  change vertex (rotateRaw r (d.1,.inr (fanPoint hkl hl d.2)))=vertex _
  apply congrArg vertex
  apply Prod.ext
  · rfl
  apply congrArg Sum.inr
  apply Subtype.ext
  exact unframe_add k l _ d.2 (0,1)

theorem rotate_turn_iterate (r : Rotation) (d : Dart) (n : ℕ) :
    rotateDart r ((Icosahedron.turn^[n]) d)=(Icosahedron.turn^[n]) (rotateDart r d) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',rotate_turn,ih]

theorem rotate_third (r : Rotation) (d : Dart) (side : Bool) :
    rotateDart r (thirdDart d side)=thirdDart (rotateDart r d) side := by
  cases side
  · exact rotate_turn_iterate r d 4
  · exact rotate_turn r d

theorem rotate_startTriangle (hkl : l<k) (hl : 0<l) (r : Rotation) (d : Dart) (side : Bool) :
    mapTriangle (rotationGraphIso r) (startTriangle hkl hl d side)=
      startTriangle hkl hl (rotateDart r d) side := by
  apply orderedTriangle_ext
  · exact rotate_parent r d
  · exact rotate_fan hkl hl r d
  · exact (rotate_fan hkl hl r (thirdDart d side)).trans
      (congrArg (fan hkl hl) (rotate_third r d side))

theorem rotate_start (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (r : Rotation) (s : Dart × Bool) :
    mapStart (rotationGraphIso r) (parametrizedStart hkl hl hprim s)=
      parametrizedStart hkl hl hprim (rotateDart r s.1,s.2) :=
  Subtype.ext (rotate_startTriangle hkl hl r s.1 s.2)

/-- These are two orbits under the actual induced graph automorphisms, not only a label partition. -/
theorem same_rotation_orbit_iff (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (s t : Dart × Bool) :
    (∃ r : Rotation, mapStart (rotationGraphIso r) (parametrizedStart hkl hl hprim s)=
      parametrizedStart hkl hl hprim t) ↔ s.2=t.2 := by
  constructor
  · rintro ⟨r,h⟩
    rw [rotate_start] at h
    have he := parametrizedStart_injective hkl hl hprim h
    have hb := congrArg (fun z : Dart × Bool => z.2) he
    exact hb
  · intro he
    obtain ⟨r,hr⟩ := rotate_transitive s.1 t.1
    refine ⟨r,?_⟩
    rw [rotate_start,hr,he]

def representative (hkl : l<k) (hl : 0<l) (side : Bool) : R002.OrderedTriangle (graph k l) :=
  startTriangle hkl hl (0,0) side

theorem exactly_two_start_orbits (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (s : Start k l) : ∃! side : Bool, ∃ r : Rotation,
      mapStart (rotationGraphIso r) (parametrizedStart hkl hl hprim ((0,0),side))=s := by
  obtain ⟨⟨d,b⟩,rfl⟩ := parametrizedStart_surjective hkl hl hprim s
  refine ⟨b,⟨d,?_⟩,?_⟩
  · rw [rotate_start,rotate_root]
  · rintro c ⟨r,hr⟩
    rw [rotate_start,rotate_root] at hr
    exact congrArg Prod.snd (parametrizedStart_injective hkl hl hprim hr)

theorem sixty_distinct_graph_rotations (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    Function.Injective (rotationGraphIso (k:=k) (l:=l)) := by
  intro r s h
  have he := congrArg (fun E => mapStart E (parametrizedStart hkl hl hprim ((0,0),false))) h
  rw [rotate_start,rotate_start,rotate_root,rotate_root] at he
  exact congrArg Prod.fst (parametrizedStart_injective hkl hl hprim he)

/-- Size of either orientation class; `same_rotation_orbit_iff` identifies it with an orbit. -/
theorem each_orbit_card (side : Bool) : Nat.card {s : Dart × Bool // s.2=side}=60 := by
  let E : Dart ≃ {s : Dart × Bool // s.2=side} := {
    toFun := fun d => ⟨(d,side),rfl⟩
    invFun := fun s => s.val.1
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨⟨d,b⟩,hb⟩; cases hb; rfl }
  rw [← Nat.card_congr E, Nat.card_eq_fintype_card]
  decide +kernel

def PathFromTriangle (t : R002.OrderedTriangle (graph k l)) : Prop :=
  ∃ n p, ClaudeChallenge.LiteralPath (graph k l) n p ∧
    p 0=t.a ∧ p 1=t.b ∧ p 2=t.c

theorem map_path_from (E : graph k l ≃g graph k l) (t : R002.OrderedTriangle (graph k l))
    (h : PathFromTriangle t) : PathFromTriangle (mapTriangle E t) := by
  obtain ⟨n,p,hp,h0,h1,h2⟩ := h
  exact ⟨n,E ∘ p,(iso_literal_path E n p).mpr hp,
    congrArg E h0,congrArg E h1,congrArg E h2⟩

theorem map_path_from_iff (E : graph k l ≃g graph k l) (t : R002.OrderedTriangle (graph k l)) :
    PathFromTriangle (mapTriangle E t) ↔ PathFromTriangle t := by
  constructor
  · intro h
    have hh := map_path_from E.symm _ h
    have ht : mapTriangle E.symm (mapTriangle E t)=t := by
      apply orderedTriangle_ext <;> exact E.symm_apply_apply _
    rwa [ht] at hh
  · exact map_path_from E t

/-- The precise reduction needed by a later positive/negative classification proof. -/
theorem all_paths_iff_two_starts (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    (∃ n p, ClaudeChallenge.LiteralPath (graph k l) n p) ↔
      ∃ side : Bool, PathFromTriangle (representative hkl hl side) := by
  constructor
  · rintro ⟨n,p,hp⟩
    obtain ⟨hn,hev,hinj,hadj,hskip,h0,hend,h1,hpen⟩ := hp
    let t : R002.OrderedTriangle (graph k l) :=
      ⟨p 0,p 1,p 2,hadj 0 (by omega),hadj 1 (by omega),(hskip 0 (by omega)).symm⟩
    let s : Start k l := ⟨t,h0,h1⟩
    obtain ⟨side,⟨r,hr⟩,_⟩ := exactly_two_start_orbits hkl hl hprim s
    refine ⟨side,(map_path_from_iff (rotationGraphIso r) _).mp ?_⟩
    have ht : mapTriangle (rotationGraphIso r) (representative hkl hl side)=t := congrArg Subtype.val hr
    rw [ht]
    exact ⟨n,p,⟨hn,hev,hinj,hadj,hskip,h0,hend,h1,hpen⟩,rfl,rfl,rfl⟩
  · rintro ⟨side,n,p,hp,_⟩
    exact ⟨n,p,hp⟩

/-- The same two research representatives decide path existence in the independent specification. -/
theorem challenge_paths_iff_two_starts (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    (∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p) ↔
      ∃ side : Bool, PathFromTriangle (representative hkl hl side) := by
  rw [← all_paths_iff_two_starts hkl hl hprim]
  let E := challengeGraphIso hkl hl hprim
  constructor
  · rintro ⟨n,p,hp⟩
    exact ⟨n,E.symm ∘ p,(iso_literal_path E.symm n p).mpr hp⟩
  · rintro ⟨n,p,hp⟩
    exact ⟨n,E ∘ p,(iso_literal_path E n p).mpr hp⟩

end R002.GCPrimitiveSurface
