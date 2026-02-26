import Wavelet.Compile.Prog

import Wavelet.Thm.Data
import Wavelet.Thm.Seq.AffineVar
import Wavelet.Thm.Dataflow.AffineChan
import Wavelet.Thm.Compile.AffineOp
import Wavelet.Thm.Compile.Fn.AffineVar

import Mathlib.Data.List.Nodup

/-! Compiling a program with each function satisfying `AffineVar`
produces a process with `AffineChan`. -/

namespace Wavelet.Compile

open Semantics Seq Dataflow

private theorem mem_linkAtomicProc_inr
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω)
  {op₂ : SigOps sigs k'}
  {inputs : Vector (LinkName χ) (Arity.ι (Sum.inr op₂))}
  {outputs : Vector (LinkName χ) (Arity.ω (Sum.inr op₂))}
  {ap : AtomicProc Op (LinkName χ) V}
  (hmem : ap ∈ linkAtomicProc k' procs (.op (.inr op₂) inputs outputs)) :
    ap = .forward (inputs.map .main) ((procs op₂.toFin').inputs.map (.dep op₂.toFin))
    ∨ (∃ ap' ∈ (procs op₂.toFin').atoms, ap = ap'.mapChans (.dep op₂.toFin))
    ∨ ap = .forward ((procs op₂.toFin').outputs.map (.dep op₂.toFin)) (outputs.map .main)
  := by
  unfold linkAtomicProc at hmem
  rcases List.mem_append.mp hmem with h₁ | h₂
  · rcases List.mem_append.mp h₁ with h₁₁ | h₁₂
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h₁₁
      exact Or.inl h₁₁
    · simp only [AtomicProcs.mapChans, List.mem_map] at h₁₂
      obtain ⟨ap', hap'_mem, rfl⟩ := h₁₂
      exact Or.inr (Or.inl ⟨ap', hap'_mem, rfl⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h₂
    exact Or.inr (Or.inr h₂)

/-- Input channels of atoms from `linkAtomicProc` (`.inr` case) are `.main`- or `.dep`-wrapped. -/
private theorem linkAtomicProc_inr_input_char
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω)
  {op₂ : SigOps sigs k'}
  {inputs : Vector (LinkName χ) (Arity.ι (Sum.inr op₂))}
  {outputs : Vector (LinkName χ) (Arity.ω (Sum.inr op₂))}
  {ap : AtomicProc Op (LinkName χ) V}
  (hmem : ap ∈ linkAtomicProc k' procs (.op (.inr op₂) inputs outputs))
  {c : LinkName χ}
  (hc : c ∈ ap.inputs) :
    (∃ n, c = .main n ∧ n ∈ inputs.toList) ∨ (∃ n, c = .dep op₂.toFin n)
  := by
  rcases mem_linkAtomicProc_inr k' procs hmem with rfl | ⟨ap', _, rfl⟩ | rfl
  · dsimp only [AtomicProc.forward, AtomicProc.inputs] at hc
    rw [Vector.toList_map] at hc
    obtain ⟨n, hn_mem, rfl⟩ := List.mem_map.mp hc
    exact Or.inl ⟨n, rfl, hn_mem⟩
  · cases ap' with
    | op o i o' =>
      dsimp only [AtomicProc.mapChans, AtomicProc.inputs] at hc
      rw [Vector.toList_map] at hc
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc; exact Or.inr ⟨n, rfl⟩
    | async aop i o' =>
      dsimp only [AtomicProc.mapChans, AtomicProc.inputs] at hc
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc; exact Or.inr ⟨n, rfl⟩
  · dsimp only [AtomicProc.forward, AtomicProc.inputs] at hc
    rw [Vector.toList_map] at hc
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc; exact Or.inr ⟨n, rfl⟩

/-- Output channels of atoms from `linkAtomicProc` (`.inr` case) are `.main`- or `.dep`-wrapped. -/
private theorem linkAtomicProc_inr_output_char
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω)
  {op₂ : SigOps sigs k'}
  {inputs : Vector (LinkName χ) (Arity.ι (Sum.inr op₂))}
  {outputs : Vector (LinkName χ) (Arity.ω (Sum.inr op₂))}
  {ap : AtomicProc Op (LinkName χ) V}
  (hmem : ap ∈ linkAtomicProc k' procs (.op (.inr op₂) inputs outputs))
  {c : LinkName χ}
  (hc : c ∈ ap.outputs) :
    (∃ n, c = .main n ∧ n ∈ outputs.toList) ∨ (∃ n, c = .dep op₂.toFin n)
  := by
  rcases mem_linkAtomicProc_inr k' procs hmem with rfl | ⟨ap', _, rfl⟩ | rfl
  · dsimp only [AtomicProc.forward, AtomicProc.outputs] at hc
    rw [Vector.toList_map] at hc
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc; exact Or.inr ⟨n, rfl⟩
  · cases ap' with
    | op o i o' =>
      dsimp only [AtomicProc.mapChans, AtomicProc.outputs] at hc
      rw [Vector.toList_map] at hc
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc; exact Or.inr ⟨n, rfl⟩
    | async aop i o' =>
      dsimp only [AtomicProc.mapChans, AtomicProc.outputs] at hc
      obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc; exact Or.inr ⟨n, rfl⟩
  · dsimp only [AtomicProc.forward, AtomicProc.outputs] at hc
    rw [Vector.toList_map] at hc
    obtain ⟨n, hn_mem, rfl⟩ := List.mem_map.mp hc
    exact Or.inl ⟨n, rfl, hn_mem⟩

/-- An `.inr` atom's I/O is disjoint from any `.main`-wrapped list with disjoint pre-images. -/
private theorem linkAtomicProc_inr_io_disjoint_main
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω)
  {op₂ : SigOps sigs k'}
  {inputs : Vector (LinkName χ) (Arity.ι (Sum.inr op₂))}
  {outputs : Vector (LinkName χ) (Arity.ω (Sum.inr op₂))}
  {ap : AtomicProc Op (LinkName χ) V}
  (hmem : ap ∈ linkAtomicProc k' procs (.op (.inr op₂) inputs outputs))
  {other_inputs other_outputs : List (LinkName χ)}
  (hdi : inputs.toList.Disjoint other_inputs)
  (hdo : outputs.toList.Disjoint other_outputs) :
    ap.inputs.Disjoint (other_inputs.map .main) ∧
    ap.outputs.Disjoint (other_outputs.map .main)
  := by
  constructor
  · intro c hc_ap hc_other
    simp only [List.mem_map] at hc_other
    obtain ⟨n', hn'_mem, rfl⟩ := hc_other
    rcases linkAtomicProc_inr_input_char k' procs hmem hc_ap with ⟨n, heq, hn⟩ | ⟨_, heq⟩
    · injection heq with heq; subst heq; exact hdi hn hn'_mem
    · nomatch heq
  · intro c hc_ap hc_other
    simp only [List.mem_map] at hc_other
    obtain ⟨n', hn'_mem, rfl⟩ := hc_other
    rcases linkAtomicProc_inr_output_char k' procs hmem hc_ap with ⟨n, heq, hn⟩ | ⟨_, heq⟩
    · injection heq with heq; subst heq; exact hdo hn hn'_mem
    · nomatch heq

/-- Two `.inr` atoms with different dep operators have disjoint I/O. -/
private theorem linkAtomicProc_inr_cross_diff_dep
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  (k' : Fin (k + 1))
  (procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω)
  {op₂a : SigOps sigs k'}
  {inputsa : Vector (LinkName χ) (Arity.ι (Sum.inr op₂a))}
  {outputsa : Vector (LinkName χ) (Arity.ω (Sum.inr op₂a))}
  {op₂b : SigOps sigs k'}
  {inputsb : Vector (LinkName χ) (Arity.ι (Sum.inr op₂b))}
  {outputsb : Vector (LinkName χ) (Arity.ω (Sum.inr op₂b))}
  (hne_op : op₂a ≠ op₂b)
  (h_pw_inputs : inputsa.toList.Disjoint inputsb.toList)
  (h_pw_outputs : outputsa.toList.Disjoint outputsb.toList)
  {x y : AtomicProc Op (LinkName χ) V}
  (hx : x ∈ linkAtomicProc k' procs (.op (.inr op₂a) inputsa outputsa))
  (hy : y ∈ linkAtomicProc k' procs (.op (.inr op₂b) inputsb outputsb)) :
    x.inputs.Disjoint y.inputs ∧ x.outputs.Disjoint y.outputs
  := by
  have hne_fin : (op₂a.toFin : Nat) ≠ (op₂b.toFin : Nat) := by
    intro h; apply hne_op
    cases op₂a; cases op₂b; simp [SigOps.toFin] at h; congr 1; exact Fin.ext h
  constructor
  · intro c hc_x hc_y
    rcases linkAtomicProc_inr_input_char k' procs hx hc_x with ⟨na, rfl, hna⟩ | ⟨na, rfl⟩
    · rcases linkAtomicProc_inr_input_char k' procs hy hc_y with ⟨nb, heq, hnb⟩ | ⟨_, heq⟩
      · injection heq with heq; subst heq; exact h_pw_inputs hna hnb
      · nomatch heq
    · rcases linkAtomicProc_inr_input_char k' procs hy hc_y with ⟨_, heq, _⟩ | ⟨_, heq⟩
      · nomatch heq
      · injection heq with hi _; exact absurd hi hne_fin
  · intro c hc_x hc_y
    rcases linkAtomicProc_inr_output_char k' procs hx hc_x with ⟨na, rfl, hna⟩ | ⟨na, rfl⟩
    · rcases linkAtomicProc_inr_output_char k' procs hy hc_y with ⟨nb, heq, hnb⟩ | ⟨_, heq⟩
      · injection heq with heq; subst heq; exact h_pw_outputs hna hnb
      · nomatch heq
    · rcases linkAtomicProc_inr_output_char k' procs hy hc_y with ⟨_, heq, _⟩ | ⟨_, heq⟩
      · nomatch heq
      · injection heq with hi _; exact absurd hi hne_fin

private theorem atomicProc_mapChans_inputs [Arity Op]
  (f : χ → χ') (ap : AtomicProc Op χ V) :
  (ap.mapChans f).inputs = ap.inputs.map f := by
  cases ap <;> simp [AtomicProc.mapChans, AtomicProc.inputs, Vector.toList_map]

private theorem atomicProc_mapChans_outputs [Arity Op]
  (f : χ → χ') (ap : AtomicProc Op χ V) :
  (ap.mapChans f).outputs = ap.outputs.map f := by
  cases ap <;> simp [AtomicProc.mapChans, AtomicProc.outputs, Vector.toList_map]

/-- Pairwise disjointness of atoms produced by `linkProcs`. -/
private theorem link_procs_atoms_pairwise
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  (k' : Fin (k + 1))
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  (haff_procs : ∀ i, (procs i).AffineChan)
  (h_atom_nodup : ∀ (a : AtomicProc (Op ⊕ SigOps sigs k') (LinkName χ) V),
    a ∈ main.atoms → a.inputs.Nodup ∧ a.outputs.Nodup)
  (h_atom_pw : main.atoms.Pairwise fun a b =>
    a.inputs.Disjoint b.inputs ∧ a.outputs.Disjoint b.outputs)
  (haff_calls : main.AffineInrOp) :
    (main.atoms.flatMap (linkAtomicProc k' procs)).Pairwise fun a b =>
      a.inputs.Disjoint b.inputs ∧ a.outputs.Disjoint b.outputs
  := by
  simp only [List.flatMap_def]
  rw [List.pairwise_flatten]
  constructor
  · intro l hl_mem
    simp only [List.mem_map] at hl_mem
    obtain ⟨atom, hatom_mem, rfl⟩ := hl_mem
    cases atom with
    | op o inputs outputs =>
      cases o with
      | inl op₁ => simp [linkAtomicProc]
      | inr op₂ =>
        simp only [linkAtomicProc]
        have hproc := haff_procs op₂.toFin'
        obtain ⟨hpi, hpo, ⟨hpa_nodup, hpa_pw⟩, hpao_di, hpai_do⟩ := hproc
        have ⟨hni, hno⟩ := h_atom_nodup _ hatom_mem
        rw [List.pairwise_append, List.pairwise_append]
        constructor
        · refine ⟨?_, ?_, ?_⟩
          · simp
          · exact List.Pairwise.map _ (fun a b ⟨hdi, hdo⟩ => ⟨
              by rw [atomicProc_mapChans_inputs, atomicProc_mapChans_inputs]
                 exact hdi.map (fun a b h => by injection h),
              by rw [atomicProc_mapChans_outputs, atomicProc_mapChans_outputs]
                 exact hdo.map (fun a b h => by injection h)⟩) hpa_pw
          · intro ap hfwd₁ b hb_mid
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hfwd₁
            subst hfwd₁
            obtain ⟨ap', hap'_mem, rfl⟩ := List.mem_map.mp hb_mid
            constructor
            · rw [atomicProc_mapChans_inputs]
              dsimp only [AtomicProc.forward, AtomicProc.inputs]
              rw [Vector.toList_map]
              exact List.disjoint_diff_map (fun _ _ => nofun)
            · rw [atomicProc_mapChans_outputs]
              conv_lhs => dsimp only [AtomicProc.forward, AtomicProc.outputs]
              rw [Vector.toList_map]
              exact (hpao_di ap' hap'_mem).symm.map (fun a b h => by injection h)
        · constructor
          · simp
          · intro ap hap _ hfwd₂_mem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hfwd₂_mem
            subst hfwd₂_mem
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hap
            rcases hap with rfl | hap_mid
            · constructor
              · dsimp only [AtomicProc.forward, AtomicProc.inputs]
                rw [Vector.toList_map, Vector.toList_map]
                exact List.disjoint_diff_map (fun _ _ => nofun)
              · dsimp only [AtomicProc.forward, AtomicProc.outputs]
                rw [Vector.toList_map, Vector.toList_map]
                exact List.disjoint_diff_map (fun _ _ => nofun)
            · obtain ⟨ap', hap'_mem, rfl⟩ := List.mem_map.mp hap_mid
              constructor
              · rw [atomicProc_mapChans_inputs]
                dsimp only [AtomicProc.forward, AtomicProc.inputs]
                rw [Vector.toList_map]
                exact (hpai_do ap' hap'_mem).map (fun a b h => by injection h)
              · rw [atomicProc_mapChans_outputs]
                dsimp only [AtomicProc.forward, AtomicProc.outputs]
                rw [Vector.toList_map]
                exact List.disjoint_diff_map (fun _ _ => nofun)
    | async aop inputs outputs => simp [linkAtomicProc]
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hlt
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map]
    intro x hx y hy
    have hne_ij : i ≠ j := by omega
    have h_pw_ij := (List.pairwise_iff_getElem.mp h_atom_pw) i j hi hj hlt
    match ha : main.atoms[i], hb : main.atoms[j] with
    | .op (.inl _) inputsa outputsa, .op (.inl _) inputsb outputsb =>
      simp [linkAtomicProc, ha] at hx; subst hx
      simp [linkAtomicProc, hb] at hy; subst hy
      simp [AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map]
      simp [ha, hb, AtomicProc.inputs, AtomicProc.outputs] at h_pw_ij
      exact ⟨h_pw_ij.1.map (fun a b h => by injection h), h_pw_ij.2.map (fun a b h => by injection h)⟩
    | .op (.inl _) inputsa outputsa, .op (.inr op₂b) inputsb outputsb =>
      simp [linkAtomicProc, ha] at hx; subst hx
      simp [ha, hb, AtomicProc.inputs, AtomicProc.outputs] at h_pw_ij
      have hd := linkAtomicProc_inr_io_disjoint_main k' procs (hb ▸ hy)
        h_pw_ij.1.symm h_pw_ij.2.symm
      simp [AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map]
      exact ⟨hd.1.symm, hd.2.symm⟩
    | .op (.inl _) inputsa outputsa, .async _ inputsb outputsb =>
      simp [linkAtomicProc, ha] at hx; subst hx
      simp [linkAtomicProc, hb] at hy; subst hy
      simp [AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map]
      simp [ha, hb, AtomicProc.inputs, AtomicProc.outputs] at h_pw_ij
      exact ⟨h_pw_ij.1.map (fun a b h => by injection h), h_pw_ij.2.map (fun a b h => by injection h)⟩
    | .op (.inr op₂a) inputsa outputsa, .op (.inl _) inputsb outputsb =>
      simp [linkAtomicProc, hb] at hy; subst hy
      simp [ha, hb, AtomicProc.inputs, AtomicProc.outputs] at h_pw_ij
      have hd := linkAtomicProc_inr_io_disjoint_main k' procs (ha ▸ hx)
        h_pw_ij.1 h_pw_ij.2
      simp [AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map]
      exact hd
    | .op (.inr op₂a) inputsa outputsa, .op (.inr op₂b) inputsb outputsb =>
      simp [ha, hb, AtomicProc.inputs, AtomicProc.outputs] at h_pw_ij
      have hne_op : op₂a ≠ op₂b := by
        have := haff_calls hne_ij hi hj ha hb
        intro heq; exact this (by subst heq; rfl)
      exact linkAtomicProc_inr_cross_diff_dep k' procs hne_op
        h_pw_ij.1 h_pw_ij.2 (ha ▸ hx) (hb ▸ hy)
    | .op (.inr op₂a) inputsa outputsa, .async _ inputsb outputsb =>
      simp [linkAtomicProc, hb] at hy; subst hy
      simp [ha, hb, AtomicProc.inputs, AtomicProc.outputs] at h_pw_ij
      have hd := linkAtomicProc_inr_io_disjoint_main k' procs (ha ▸ hx)
        h_pw_ij.1 h_pw_ij.2
      simp [AtomicProc.inputs, AtomicProc.outputs]
      exact hd
    | .async _ inputsa outputsa, .op (.inl _) inputsb outputsb =>
      simp [linkAtomicProc, ha] at hx; subst hx
      simp [linkAtomicProc, hb] at hy; subst hy
      simp [AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map]
      simp [ha, hb, AtomicProc.inputs, AtomicProc.outputs] at h_pw_ij
      exact ⟨h_pw_ij.1.map (fun a b h => by injection h), h_pw_ij.2.map (fun a b h => by injection h)⟩
    | .async _ inputsa outputsa, .op (.inr op₂b) inputsb outputsb =>
      simp [linkAtomicProc, ha] at hx; subst hx
      simp [ha, hb, AtomicProc.inputs, AtomicProc.outputs] at h_pw_ij
      have hd := linkAtomicProc_inr_io_disjoint_main k' procs (hb ▸ hy)
        h_pw_ij.1.symm h_pw_ij.2.symm
      simp [AtomicProc.inputs, AtomicProc.outputs]
      exact ⟨hd.1.symm, hd.2.symm⟩
    | .async _ inputsa outputsa, .async _ inputsb outputsb =>
      simp [linkAtomicProc, ha] at hx; subst hx
      simp [linkAtomicProc, hb] at hy; subst hy
      simp [AtomicProc.inputs, AtomicProc.outputs]
      simp [ha, hb, AtomicProc.inputs, AtomicProc.outputs] at h_pw_ij
      exact ⟨h_pw_ij.1.map (fun a b h => by injection h), h_pw_ij.2.map (fun a b h => by injection h)⟩

/-- Atom outputs are disjoint from proc inputs in `linkProcs`. -/
private theorem link_procs_outputs_disjoint
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  (k' : Fin (k + 1))
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  (hdisj : ∀ (a : AtomicProc (Op ⊕ SigOps sigs k') (LinkName χ) V),
    a ∈ main.atoms → a.outputs.Disjoint main.inputs.toList) :
    ∀ (ap : AtomicProc Op (LinkName χ) V),
      ap ∈ main.atoms.flatMap (linkAtomicProc k' procs) →
      ap.outputs.Disjoint (main.inputs.map LinkName.main).toList := by
  intro ap hap
  simp only [List.flatMap_def] at hap
  rw [List.mem_flatten] at hap
  obtain ⟨l, hl_mem, hap_mem⟩ := hap
  simp only [List.mem_map] at hl_mem
  obtain ⟨atom, hatom_mem, rfl⟩ := hl_mem
  rw [Vector.toList_map]
  cases atom with
  | op o inputs outputs =>
    cases o with
    | inl op₁ =>
      simp [linkAtomicProc] at hap_mem; subst hap_mem
      simp [AtomicProc.outputs, Vector.toList_map]
      exact (hdisj _ hatom_mem).map (fun a b h => by injection h)
    | inr op₂ =>
      rcases mem_linkAtomicProc_inr k' procs hap_mem with rfl | ⟨ap', _, rfl⟩ | rfl
      · simp [AtomicProc.forward, AtomicProc.outputs, Vector.toList_map]
        exact List.disjoint_diff_map (fun _ _ => nofun)
      · rw [atomicProc_mapChans_outputs]
        exact List.disjoint_diff_map (fun _ _ => nofun)
      · simp [AtomicProc.forward, AtomicProc.outputs, Vector.toList_map]
        exact (hdisj _ hatom_mem).map (fun a b h => by injection h)
  | async aop inputs outputs =>
    simp [linkAtomicProc] at hap_mem; subst hap_mem
    simp [AtomicProc.outputs]
    exact (hdisj _ hatom_mem).map (fun a b h => by injection h)

/-- Atom inputs are disjoint from proc outputs in `linkProcs`. -/
private theorem link_procs_inputs_disjoint
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  (k' : Fin (k + 1))
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  (hdisj : ∀ (a : AtomicProc (Op ⊕ SigOps sigs k') (LinkName χ) V),
    a ∈ main.atoms → a.inputs.Disjoint main.outputs.toList) :
    ∀ (ap : AtomicProc Op (LinkName χ) V),
      ap ∈ main.atoms.flatMap (linkAtomicProc k' procs) →
      ap.inputs.Disjoint (main.outputs.map LinkName.main).toList := by
  intro ap hap
  simp only [List.flatMap_def] at hap
  rw [List.mem_flatten] at hap
  obtain ⟨l, hl_mem, hap_mem⟩ := hap
  simp only [List.mem_map] at hl_mem
  obtain ⟨atom, hatom_mem, rfl⟩ := hl_mem
  rw [Vector.toList_map]
  cases atom with
  | op o inputs outputs =>
    cases o with
    | inl op₁ =>
      simp [linkAtomicProc] at hap_mem; subst hap_mem
      simp [AtomicProc.inputs, Vector.toList_map]
      exact (hdisj _ hatom_mem).map (fun a b h => by injection h)
    | inr op₂ =>
      rcases mem_linkAtomicProc_inr k' procs hap_mem with rfl | ⟨ap', _, rfl⟩ | rfl
      · simp [AtomicProc.forward, AtomicProc.inputs, Vector.toList_map]
        exact (hdisj _ hatom_mem).map (fun a b h => by injection h)
      · rw [atomicProc_mapChans_inputs]
        exact List.disjoint_diff_map (fun _ _ => nofun)
      · simp [AtomicProc.forward, AtomicProc.inputs, Vector.toList_map]
        exact List.disjoint_diff_map (fun _ _ => nofun)
  | async aop inputs outputs =>
    simp [linkAtomicProc] at hap_mem; subst hap_mem
    simp [AtomicProc.inputs]
    exact (hdisj _ hatom_mem).map (fun a b h => by injection h)

/-- `linkProcs` preserves the affineness of channel names. -/
theorem link_procs_preserves_aff_var
  [Arity Op] [NeZeroArity Op]
  {sigs : Sigs k} [NeZeroSigs sigs]
  (k' : Fin (k + 1))
  {procs : (i : Fin k') → Proc Op (LinkName χ) V (sigs ↓i).ι (sigs ↓i).ω}
  {main : Proc (Op ⊕ SigOps sigs k') (LinkName χ) V m n}
  (haff_procs : ∀ i, (procs i).AffineChan)
  (haff_main : main.AffineChan)
  (haff_calls : main.AffineInrOp) :
    (linkProcs k' procs main).AffineChan
  := by
  obtain ⟨h_in, h_out, ⟨h_atom_nodup, h_atom_pw⟩, hdisj₁, hdisj₂⟩ := haff_main
  simp only [Proc.AffineChan, linkProcs]
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Vector.toList_map]; exact h_in.map (fun a b h => by injection h)
  · rw [Vector.toList_map]; exact h_out.map (fun a b h => by injection h)
  · intro ap hap
    rw [List.mem_flatten] at hap
    obtain ⟨l, hl_mem, hap_mem⟩ := hap
    simp only [List.mem_map] at hl_mem
    obtain ⟨atom, hatom_mem, rfl⟩ := hl_mem
    cases atom with
    | op o inputs outputs =>
      cases o with
      | inl op₁ =>
        simp [linkAtomicProc] at hap_mem; subst hap_mem
        have ⟨hni, hno⟩ := h_atom_nodup _ hatom_mem
        simp [AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map]
        exact ⟨hni.map (fun a b h => by injection h), hno.map (fun a b h => by injection h)⟩
      | inr op₂ =>
        have hproc := haff_procs op₂.toFin'
        obtain ⟨hpi, hpo, ⟨hpa_nodup, _⟩, _, _⟩ := hproc
        have ⟨hni, hno⟩ := h_atom_nodup _ hatom_mem
        rcases mem_linkAtomicProc_inr k' procs hap_mem with rfl | ⟨ap', hap'_mem, rfl⟩ | rfl
        · simp [AtomicProc.forward, AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map]
          exact ⟨hni.map (fun a b h => by injection h), hpi.map (fun a b h => by injection h)⟩
        · constructor
          · rw [atomicProc_mapChans_inputs]
            exact (hpa_nodup ap' hap'_mem).1.map (fun a b h => by injection h)
          · rw [atomicProc_mapChans_outputs]
            exact (hpa_nodup ap' hap'_mem).2.map (fun a b h => by injection h)
        · simp [AtomicProc.forward, AtomicProc.inputs, AtomicProc.outputs, Vector.toList_map]
          exact ⟨hpo.map (fun a b h => by injection h), hno.map (fun a b h => by injection h)⟩
    | async aop inputs outputs =>
      simp [linkAtomicProc] at hap_mem; subst hap_mem
      have ⟨hni, hno⟩ := h_atom_nodup _ hatom_mem
      simp [AtomicProc.inputs, AtomicProc.outputs]
      exact ⟨hni.map (fun a b h => by injection h), hno.map (fun a b h => by injection h)⟩
  · exact link_procs_atoms_pairwise k' haff_procs h_atom_nodup h_atom_pw haff_calls
  · exact link_procs_outputs_disjoint k' hdisj₁
  · exact link_procs_inputs_disjoint k' hdisj₂

theorem compile_prog_preserves_aff_var
  [Arity Op] [NeZeroArity Op] [DecidableEq χ] [InterpConsts V]
  {sigs : Sigs k} [instNZ : NeZeroSigs sigs]
  {prog : Prog Op χ V sigs}
  {i : Fin k}
  (haff_var : prog.AffineVar)
  (haff_op : prog.AffineInrOp) :
    (compileProg prog i).AffineChan
  := by
  unfold compileProg
  apply link_procs_preserves_aff_var
  · intros i
    apply compile_prog_preserves_aff_var haff_var haff_op
  · apply map_chans_preserves_aff_var (by simp [Function.Injective])
    exact compile_fn_preserves_aff_var (prog i) (haff_var i)
  · apply map_chans_preserves_aff_op
    apply compile_fn_preserves_aff_op
    exact haff_op i

end Wavelet.Compile
