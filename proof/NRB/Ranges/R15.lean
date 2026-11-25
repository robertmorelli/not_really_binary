import NRB.Sweep

theorem r15_ok : blocks 16384 65536 16106130360 = true := by native_decide

theorem r15 : cover 16106130360 17179872184 := blocks_sound 16384 65536 16106130360 r15_ok
