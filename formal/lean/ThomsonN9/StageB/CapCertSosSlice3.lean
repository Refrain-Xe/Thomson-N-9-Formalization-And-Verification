import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSlice3

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_3 : checkKronCapAtT (wForT 3) 3 = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSlice3
