import D2RelationGap.Words

/-! Literal transcription of the six existing JSON certificates.
Acceptance is a finite computation; soundness in PresentedGroup is proved in SourceIdentities. -/
namespace D2RelationGap

def wordTraces : List WordTrace :=
[
  ⟨[pos .x1, pos .x1],
   [pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2],
   [⟨2, 2, 0, false⟩]⟩,
  ⟨[pos .x2, pos .x2, pos .x2, pos .a2, neg .x2, neg .x2, neg .x2],
   [pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2, pos .a2],
   [⟨1, 1, 2, false⟩, ⟨1, 3, 1, false⟩, ⟨1, 9, 0, false⟩]⟩,
  ⟨[pos .x1, pos .x1, pos .a1, neg .x1, neg .x1],
   [pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1],
   [⟨0, 1, 1, false⟩, ⟨0, 4, 0, false⟩]⟩,
  ⟨[pos .s, pos .x2, pos .x2, pos .x2, neg .s],
   [pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1, pos .a1],
   [⟨3, 3, 0, false⟩]⟩,
  ⟨[pos .x2, pos .x2, pos .x2, pos .a2, neg .x2, neg .x2, neg .x2, neg .a2],
   [pos .x1, pos .x1],
   [⟨1, 1, 2, false⟩, ⟨1, 3, 1, false⟩, ⟨1, 9, 0, false⟩, ⟨2, 2, 0, true⟩]⟩,
  ⟨[pos .x1, pos .x1, pos .a1, neg .x1, neg .x1, neg .a1],
   [pos .s, pos .x2, pos .x2, pos .x2, neg .s],
   [⟨0, 1, 1, false⟩, ⟨0, 4, 0, false⟩, ⟨3, 3, 0, true⟩]⟩
]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem source_traces_replay : wordTraces.all checkTrace = true := by decide

/-- One deliberate corruption must be rejected. -/
theorem bad_rule_rejected : rewriteStep t1 ⟨99, 1, 0, false⟩ = none := by decide

theorem wrong_target_rejected :
    checkTrace ⟨t1, [], [⟨2, 2, 0, false⟩]⟩ = false := by decide

/-- A valid rule with a corrupted exponent must also fail. -/
theorem wrong_power_rejected :
    checkTrace ⟨t1, List.replicate 26 (pos .a2), [⟨2, 1, 0, false⟩]⟩ = false := by decide

end D2RelationGap
