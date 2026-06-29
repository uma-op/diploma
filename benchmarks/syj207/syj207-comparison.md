# syj207 Comparison: Current Prover vs intuitR

Chart: `benchmarks/syj207/syj207-comparison.svg`

| N | current result | current total ms | intuitR result | intuitR reported total ms | intuitR wall ms |
| ---: | --- | ---: | --- | ---: | ---: |
| 1 | invalid | 37.943 | invalid | 0.000 | 15.124 |
| 2 | invalid | 70.920 | invalid | 1.000 | 15.345 |
| 3 | invalid | 341.367 | invalid | 2.000 | 14.953 |
| 4 | invalid | 132445.618 | invalid | 2.000 | 15.538 |
| 5 | invalid | 8638.917 | invalid | 5.000 | 25.558 |

Both provers classify all N=1..5 as invalid. Prototype time peaks at N=4 (~132 s); intuitR stays in single-digit milliseconds.
