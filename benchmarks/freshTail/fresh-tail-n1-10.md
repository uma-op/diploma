# fresh-tail Phase Timings (N=1..10)

Chart: `benchmarks/freshTail/fresh-tail-n1-10.svg`

| N | result | clausification ms | proving ms | annotation ms | total ms |
| ---: | --- | ---: | ---: | ---: | ---: |
| 1 | valid | 1.572 | 102.166 | 0.328 | 104.067 |
| 2 | valid | 1.246 | 69.615 | 0.292 | 71.154 |
| 3 | valid | 1.595 | 120.272 | 0.273 | 122.141 |
| 4 | valid | 1.326 | 90.854 | 0.253 | 92.433 |
| 5 | valid | 1.638 | 114.847 | 0.280 | 116.766 |
| 6 | valid | 1.313 | 131.123 | 0.243 | 132.680 |
| 7 | valid | 1.948 | 150.566 | 0.271 | 152.786 |
| 8 | valid | 1.644 | 145.506 | 0.278 | 147.429 |
| 9 | valid | 1.712 | 171.318 | 0.341 | 173.371 |
| 10 | valid | 2.281 | 181.947 | 0.277 | 184.506 |

All formulas valid. Base X = syj201(1); each N adds N fresh-atom tails `(body => p) => p`.
