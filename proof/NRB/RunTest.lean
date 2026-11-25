import NRB.Runs

/-! A worked instance of the stripe filter: runs of 13 lengths spaced 577,237 apart,
    three blocks, starting at length 3000. -/

theorem rt : rsweep 577237 12 3 3000 = true := by native_decide

theorem rt_cover : cover 3000 (3000 + 3 * (577237 * (12 + 1))) := rsweep_sound 577237 12 3 3000 rt

#print axioms rsweep_sound
#print axioms rt_cover
