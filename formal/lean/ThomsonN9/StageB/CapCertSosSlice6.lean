import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSlice6

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_6 : checkKronCapAtT (wForT 6) 6 = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSlice6
