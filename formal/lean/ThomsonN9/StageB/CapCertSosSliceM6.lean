import ThomsonN9.StageB.CapCertSosData

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace ThomsonN9.StageB.CapCertSosSliceM6

open ThomsonN9.StageB.CapCertSosData

theorem kron_t_m6 : checkKronCapAtT (wForT (-6 : ℤ)) (-6 : ℤ) = true := by decide +kernel

end ThomsonN9.StageB.CapCertSosSliceM6
