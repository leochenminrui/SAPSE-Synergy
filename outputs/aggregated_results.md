# Synergy Experiment Results

## Aggregated Results Table

| Configuration | Guards | Verified (%) | Abstained (%) | Avg Time (s) | URC (Sum) |
|---------------|--------|--------------|---------------|--------------|----------|
| Baseline-RAG | None | 37.6% (752/2000) | 0.0% (0/2000) | 0.142 | 0 |
| SAPSE-Strict | VC-Guarded | 37.3% (746/2000) | 5.3% (106/2000) | 0.112 | 0 |
| SAPSE-Fast | None | 32.8% (656/2000) | 0.0% (0/2000) | 0.094 | 0 |
| SAPSE-Synergy | UP-Unguarded → VC-Guarded | 32.8% (656/2000) | 0.1% (1/2000) | 0.092 | 0 |

## Detailed Statistics

### Baseline-RAG

- **Total items**: 2000
- **Verified**: 752 (37.6%)
- **Abstained**: 0 (0.0%)
- **Failed**: 1248
- **Average time**: 0.142s
- **URC count**: 0

### SAPSE-Strict

- **Total items**: 2000
- **Verified**: 746 (37.3%)
- **Abstained**: 106 (5.3%)
- **Failed**: 1148
- **Average time**: 0.112s
- **URC count**: 0

### SAPSE-Fast

- **Total items**: 2000
- **Verified**: 656 (32.8%)
- **Abstained**: 0 (0.0%)
- **Failed**: 1344
- **Average time**: 0.094s
- **URC count**: 0

### SAPSE-Synergy

- **Total items**: 2000
- **Verified**: 656 (32.8%)
- **Abstained**: 1 (0.1%)
- **Failed**: 1343
- **Average time**: 0.092s
- **URC count**: 0

