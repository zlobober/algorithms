=== Iteration state ===
Time: 0
TotalX: 0
TotalPi: 0
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Matching: 
Pi:
0: 0
1: 0
2: 0
3: 0
4: 0
5: 0
6: 0
7: 0
8: 0
9: 0
10: 0
11: 0
12: 0
13: 0
Blossoms:
AdjustedWeights:
0 60 42 142 66 0 190 190 178 16 10 176 128 192 
60 0 50 32 38 30 80 130 184 180 76 42 6 38 
42 50 0 32 38 82 50 128 40 16 102 162 38 110 
142 32 32 0 24 112 16 86 188 174 110 124 160 82 
66 38 38 24 0 158 12 24 174 6 184 128 74 188 
0 30 82 112 158 0 96 74 36 20 144 98 112 108 
190 80 50 16 12 96 0 172 192 24 118 200 134 86 
190 130 128 86 24 74 172 0 50 64 146 60 86 132 
178 184 40 188 174 36 192 50 0 24 74 52 48 70 
16 180 16 174 6 20 24 64 24 0 156 170 26 34 
10 76 102 110 184 144 118 146 74 156 0 134 176 102 
176 42 162 124 128 98 200 60 52 170 134 0 128 12 
128 6 38 160 74 112 134 86 48 26 176 128 0 130 
192 38 110 82 188 108 86 132 70 34 102 12 130 0 
=======================
Iteration started (Time: 1)
Trying to make primal step
Running DFS (v: 0)
Found alternating path (v: 0, u: 5, TotalX: 0 -> 1)
! Alternating path: 
5 0
Path alternated
=== Iteration state ===
Time: 1
TotalX: 1
TotalPi: 0
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 1 2 3 4 6 7 8 9 10 11 12 13 
Matching: (5 0) 
Pi:
0: 0
1: 0
2: 0
3: 0
4: 0
5: 0
6: 0
7: 0
8: 0
9: 0
10: 0
11: 0
12: 0
13: 0
Blossoms:
AdjustedWeights:
0 60 42 142 66 0 190 190 178 16 10 176 128 192 
60 0 50 32 38 30 80 130 184 180 76 42 6 38 
42 50 0 32 38 82 50 128 40 16 102 162 38 110 
142 32 32 0 24 112 16 86 188 174 110 124 160 82 
66 38 38 24 0 158 12 24 174 6 184 128 74 188 
0 30 82 112 158 0 96 74 36 20 144 98 112 108 
190 80 50 16 12 96 0 172 192 24 118 200 134 86 
190 130 128 86 24 74 172 0 50 64 146 60 86 132 
178 184 40 188 174 36 192 50 0 24 74 52 48 70 
16 180 16 174 6 20 24 64 24 0 156 170 26 34 
10 76 102 110 184 144 118 146 74 156 0 134 176 102 
176 42 162 124 128 98 200 60 52 170 134 0 128 12 
128 6 38 160 74 112 134 86 48 26 176 128 0 130 
192 38 110 82 188 108 86 132 70 34 102 12 130 0 
=======================
Iteration started (Time: 2)
Trying to make primal step
Running DFS (v: 1)
Running DFS (v: 2)
Running DFS (v: 3)
Running DFS (v: 4)
Running DFS (v: 6)
Running DFS (v: 7)
Running DFS (v: 8)
Running DFS (v: 9)
Running DFS (v: 10)
Running DFS (v: 11)
Running DFS (v: 12)
Running DFS (v: 13)
Did not find alternating path nor blossom
Making dual step
Tightest odd blossom (BlossomId: -1, Limit: 100000000)
Tightest even-even edge (v: 1, u: 12, Limit: 3)
Tightest even-out edge (v: 10, u: 0 Limit: 10)
Modifying dual solution (epsilon: 3)
=== Iteration state ===
Time: 2
TotalX: 1
TotalPi: 36
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 1 2 3 4 6 7 8 9 10 11 12 13 
Matching: (5 0) 
Pi:
0: 0
1: 3
2: 3
3: 3
4: 3
5: 0
6: 3
7: 3
8: 3
9: 3
10: 3
11: 3
12: 3
13: 3
Blossoms:
AdjustedWeights:
0 57 39 139 63 0 187 187 175 13 7 173 125 189 
57 0 44 26 32 27 74 124 178 174 70 36 0 32 
39 44 0 26 32 79 44 122 34 10 96 156 32 104 
139 26 26 0 18 109 10 80 182 168 104 118 154 76 
63 32 32 18 0 155 6 18 168 0 178 122 68 182 
0 27 79 109 155 0 93 71 33 17 141 95 109 105 
187 74 44 10 6 93 0 166 186 18 112 194 128 80 
187 124 122 80 18 71 166 0 44 58 140 54 80 126 
175 178 34 182 168 33 186 44 0 18 68 46 42 64 
13 174 10 168 0 17 18 58 18 0 150 164 20 28 
7 70 96 104 178 141 112 140 68 150 0 128 170 96 
173 36 156 118 122 95 194 54 46 164 128 0 122 6 
125 0 32 154 68 109 128 80 42 20 170 122 0 124 
189 32 104 76 182 105 80 126 64 28 96 6 124 0 
=======================
Iteration started (Time: 3)
Trying to make primal step
Running DFS (v: 1)
Found alternating path (v: 1, u: 12, TotalX: 1 -> 2)
! Alternating path: 
12 1
Path alternated
=== Iteration state ===
Time: 3
TotalX: 2
TotalPi: 36
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 3 4 6 7 8 9 10 11 13 
Matching: (5 0) (12 1) 
Pi:
0: 0
1: 3
2: 3
3: 3
4: 3
5: 0
6: 3
7: 3
8: 3
9: 3
10: 3
11: 3
12: 3
13: 3
Blossoms:
AdjustedWeights:
0 57 39 139 63 0 187 187 175 13 7 173 125 189 
57 0 44 26 32 27 74 124 178 174 70 36 0 32 
39 44 0 26 32 79 44 122 34 10 96 156 32 104 
139 26 26 0 18 109 10 80 182 168 104 118 154 76 
63 32 32 18 0 155 6 18 168 0 178 122 68 182 
0 27 79 109 155 0 93 71 33 17 141 95 109 105 
187 74 44 10 6 93 0 166 186 18 112 194 128 80 
187 124 122 80 18 71 166 0 44 58 140 54 80 126 
175 178 34 182 168 33 186 44 0 18 68 46 42 64 
13 174 10 168 0 17 18 58 18 0 150 164 20 28 
7 70 96 104 178 141 112 140 68 150 0 128 170 96 
173 36 156 118 122 95 194 54 46 164 128 0 122 6 
125 0 32 154 68 109 128 80 42 20 170 122 0 124 
189 32 104 76 182 105 80 126 64 28 96 6 124 0 
=======================
Iteration started (Time: 4)
Trying to make primal step
Running DFS (v: 2)
Running DFS (v: 3)
Running DFS (v: 4)
Found alternating path (v: 4, u: 9, TotalX: 2 -> 3)
! Alternating path: 
9 4
Path alternated
=== Iteration state ===
Time: 4
TotalX: 3
TotalPi: 36
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 3 6 7 8 10 11 13 
Matching: (5 0) (9 4) (12 1) 
Pi:
0: 0
1: 3
2: 3
3: 3
4: 3
5: 0
6: 3
7: 3
8: 3
9: 3
10: 3
11: 3
12: 3
13: 3
Blossoms:
AdjustedWeights:
0 57 39 139 63 0 187 187 175 13 7 173 125 189 
57 0 44 26 32 27 74 124 178 174 70 36 0 32 
39 44 0 26 32 79 44 122 34 10 96 156 32 104 
139 26 26 0 18 109 10 80 182 168 104 118 154 76 
63 32 32 18 0 155 6 18 168 0 178 122 68 182 
0 27 79 109 155 0 93 71 33 17 141 95 109 105 
187 74 44 10 6 93 0 166 186 18 112 194 128 80 
187 124 122 80 18 71 166 0 44 58 140 54 80 126 
175 178 34 182 168 33 186 44 0 18 68 46 42 64 
13 174 10 168 0 17 18 58 18 0 150 164 20 28 
7 70 96 104 178 141 112 140 68 150 0 128 170 96 
173 36 156 118 122 95 194 54 46 164 128 0 122 6 
125 0 32 154 68 109 128 80 42 20 170 122 0 124 
189 32 104 76 182 105 80 126 64 28 96 6 124 0 
=======================
Iteration started (Time: 5)
Trying to make primal step
Running DFS (v: 2)
Running DFS (v: 3)
Running DFS (v: 6)
Running DFS (v: 7)
Running DFS (v: 8)
Running DFS (v: 10)
Running DFS (v: 11)
Running DFS (v: 13)
Did not find alternating path nor blossom
Making dual step
Tightest odd blossom (BlossomId: -1, Limit: 100000000)
Tightest even-even edge (v: 11, u: 13, Limit: 3)
Tightest even-out edge (v: 6, u: 4 Limit: 6)
Modifying dual solution (epsilon: 3)
=== Iteration state ===
Time: 5
TotalX: 3
TotalPi: 60
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 3 6 7 8 10 11 13 
Matching: (5 0) (9 4) (12 1) 
Pi:
0: 0
1: 3
2: 6
3: 6
4: 3
5: 0
6: 6
7: 6
8: 6
9: 3
10: 6
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 57 36 136 63 0 184 184 172 13 4 170 125 186 
57 0 41 23 32 27 71 121 175 174 67 33 0 29 
36 41 0 20 29 76 38 116 28 7 90 150 29 98 
136 23 20 0 15 106 4 74 176 165 98 112 151 70 
63 32 29 15 0 155 3 15 165 0 175 119 68 179 
0 27 76 106 155 0 90 68 30 17 138 92 109 102 
184 71 38 4 3 90 0 160 180 15 106 188 125 74 
184 121 116 74 15 68 160 0 38 55 134 48 77 120 
172 175 28 176 165 30 180 38 0 15 62 40 39 58 
13 174 7 165 0 17 15 55 15 0 147 161 20 25 
4 67 90 98 175 138 106 134 62 147 0 122 167 90 
170 33 150 112 119 92 188 48 40 161 122 0 119 0 
125 0 29 151 68 109 125 77 39 20 167 119 0 121 
186 29 98 70 179 102 74 120 58 25 90 0 121 0 
=======================
Iteration started (Time: 6)
Trying to make primal step
Running DFS (v: 2)
Running DFS (v: 3)
Running DFS (v: 6)
Running DFS (v: 7)
Running DFS (v: 8)
Running DFS (v: 10)
Running DFS (v: 11)
Found alternating path (v: 11, u: 13, TotalX: 3 -> 4)
! Alternating path: 
13 11
Path alternated
=== Iteration state ===
Time: 6
TotalX: 4
TotalPi: 60
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 3 6 7 8 10 
Matching: (5 0) (9 4) (12 1) (13 11) 
Pi:
0: 0
1: 3
2: 6
3: 6
4: 3
5: 0
6: 6
7: 6
8: 6
9: 3
10: 6
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 57 36 136 63 0 184 184 172 13 4 170 125 186 
57 0 41 23 32 27 71 121 175 174 67 33 0 29 
36 41 0 20 29 76 38 116 28 7 90 150 29 98 
136 23 20 0 15 106 4 74 176 165 98 112 151 70 
63 32 29 15 0 155 3 15 165 0 175 119 68 179 
0 27 76 106 155 0 90 68 30 17 138 92 109 102 
184 71 38 4 3 90 0 160 180 15 106 188 125 74 
184 121 116 74 15 68 160 0 38 55 134 48 77 120 
172 175 28 176 165 30 180 38 0 15 62 40 39 58 
13 174 7 165 0 17 15 55 15 0 147 161 20 25 
4 67 90 98 175 138 106 134 62 147 0 122 167 90 
170 33 150 112 119 92 188 48 40 161 122 0 119 0 
125 0 29 151 68 109 125 77 39 20 167 119 0 121 
186 29 98 70 179 102 74 120 58 25 90 0 121 0 
=======================
Iteration started (Time: 7)
Trying to make primal step
Running DFS (v: 2)
Running DFS (v: 3)
Running DFS (v: 6)
Running DFS (v: 7)
Running DFS (v: 8)
Running DFS (v: 10)
Did not find alternating path nor blossom
Making dual step
Tightest odd blossom (BlossomId: -1, Limit: 100000000)
Tightest even-even edge (v: 3, u: 6, Limit: 2)
Tightest even-out edge (v: 6, u: 4 Limit: 3)
Modifying dual solution (epsilon: 2)
=== Iteration state ===
Time: 7
TotalX: 4
TotalPi: 72
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 3 6 7 8 10 
Matching: (5 0) (9 4) (12 1) (13 11) 
Pi:
0: 0
1: 3
2: 8
3: 8
4: 3
5: 0
6: 8
7: 8
8: 8
9: 3
10: 8
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 57 34 134 63 0 182 182 170 13 2 170 125 186 
57 0 39 21 32 27 69 119 173 174 65 33 0 29 
34 39 0 16 27 74 34 112 24 5 86 148 27 96 
134 21 16 0 13 104 0 70 172 163 94 110 149 68 
63 32 27 13 0 155 1 13 163 0 173 119 68 179 
0 27 74 104 155 0 88 66 28 17 136 92 109 102 
182 69 34 0 1 88 0 156 176 13 102 186 123 72 
182 119 112 70 13 66 156 0 34 53 130 46 75 118 
170 173 24 172 163 28 176 34 0 13 58 38 37 56 
13 174 5 163 0 17 13 53 13 0 145 161 20 25 
2 65 86 94 173 136 102 130 58 145 0 120 165 88 
170 33 148 110 119 92 186 46 38 161 120 0 119 0 
125 0 27 149 68 109 123 75 37 20 165 119 0 121 
186 29 96 68 179 102 72 118 56 25 88 0 121 0 
=======================
Iteration started (Time: 8)
Trying to make primal step
Running DFS (v: 2)
Running DFS (v: 3)
Found alternating path (v: 3, u: 6, TotalX: 4 -> 5)
! Alternating path: 
6 3
Path alternated
=== Iteration state ===
Time: 8
TotalX: 5
TotalPi: 72
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 7 8 10 
Matching: (5 0) (6 3) (9 4) (12 1) (13 11) 
Pi:
0: 0
1: 3
2: 8
3: 8
4: 3
5: 0
6: 8
7: 8
8: 8
9: 3
10: 8
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 57 34 134 63 0 182 182 170 13 2 170 125 186 
57 0 39 21 32 27 69 119 173 174 65 33 0 29 
34 39 0 16 27 74 34 112 24 5 86 148 27 96 
134 21 16 0 13 104 0 70 172 163 94 110 149 68 
63 32 27 13 0 155 1 13 163 0 173 119 68 179 
0 27 74 104 155 0 88 66 28 17 136 92 109 102 
182 69 34 0 1 88 0 156 176 13 102 186 123 72 
182 119 112 70 13 66 156 0 34 53 130 46 75 118 
170 173 24 172 163 28 176 34 0 13 58 38 37 56 
13 174 5 163 0 17 13 53 13 0 145 161 20 25 
2 65 86 94 173 136 102 130 58 145 0 120 165 88 
170 33 148 110 119 92 186 46 38 161 120 0 119 0 
125 0 27 149 68 109 123 75 37 20 165 119 0 121 
186 29 96 68 179 102 72 118 56 25 88 0 121 0 
=======================
Iteration started (Time: 9)
Trying to make primal step
Running DFS (v: 2)
Running DFS (v: 7)
Running DFS (v: 8)
Running DFS (v: 10)
Did not find alternating path nor blossom
Making dual step
Tightest odd blossom (BlossomId: -1, Limit: 100000000)
Tightest even-even edge (v: 2, u: 8, Limit: 12)
Tightest even-out edge (v: 10, u: 0 Limit: 2)
Modifying dual solution (epsilon: 2)
=== Iteration state ===
Time: 9
TotalX: 5
TotalPi: 80
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 7 8 10 
Matching: (5 0) (6 3) (9 4) (12 1) (13 11) 
Pi:
0: 0
1: 3
2: 10
3: 8
4: 3
5: 0
6: 8
7: 10
8: 10
9: 3
10: 10
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 57 32 134 63 0 182 180 168 13 0 170 125 186 
57 0 37 21 32 27 69 117 171 174 63 33 0 29 
32 37 0 14 25 72 32 108 20 3 82 146 25 94 
134 21 14 0 13 104 0 68 170 163 92 110 149 68 
63 32 25 13 0 155 1 11 161 0 171 119 68 179 
0 27 72 104 155 0 88 64 26 17 134 92 109 102 
182 69 32 0 1 88 0 154 174 13 100 186 123 72 
180 117 108 68 11 64 154 0 30 51 126 44 73 116 
168 171 20 170 161 26 174 30 0 11 54 36 35 54 
13 174 3 163 0 17 13 51 11 0 143 161 20 25 
0 63 82 92 171 134 100 126 54 143 0 118 163 86 
170 33 146 110 119 92 186 44 36 161 118 0 119 0 
125 0 25 149 68 109 123 73 35 20 163 119 0 121 
186 29 94 68 179 102 72 116 54 25 86 0 121 0 
=======================
Iteration started (Time: 10)
Trying to make primal step
Running DFS (v: 2)
Running DFS (v: 7)
Running DFS (v: 8)
Running DFS (v: 10)
Did not find alternating path nor blossom
Making dual step
Tightest odd blossom (BlossomId: -1, Limit: 100000000)
Tightest even-even edge (v: 2, u: 8, Limit: 10)
Tightest even-out edge (v: 2, u: 9 Limit: 3)
Modifying dual solution (epsilon: 3)
=== Iteration state ===
Time: 10
TotalX: 5
TotalPi: 92
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 7 8 10 
Matching: (5 0) (6 3) (9 4) (12 1) (13 11) 
Pi:
0: -3
1: 3
2: 13
3: 8
4: 3
5: 3
6: 8
7: 13
8: 13
9: 3
10: 13
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 60 32 137 66 0 185 180 168 16 0 173 128 189 
60 0 34 21 32 24 69 114 168 174 60 33 0 29 
32 34 0 11 22 66 29 102 14 0 76 143 22 91 
137 21 11 0 13 101 0 65 167 163 89 110 149 68 
66 32 22 13 0 152 1 8 158 0 168 119 68 179 
0 24 66 101 152 0 85 58 20 14 128 89 106 99 
185 69 29 0 1 85 0 151 171 13 97 186 123 72 
180 114 102 65 8 58 151 0 24 48 120 41 70 113 
168 168 14 167 158 20 171 24 0 8 48 33 32 51 
16 174 0 163 0 14 13 48 8 0 140 161 20 25 
0 60 76 89 168 128 97 120 48 140 0 115 160 83 
173 33 143 110 119 89 186 41 33 161 115 0 119 0 
128 0 22 149 68 106 123 70 32 20 160 119 0 121 
189 29 91 68 179 99 72 113 51 25 83 0 121 0 
=======================
Iteration started (Time: 11)
Trying to make primal step
Running DFS (v: 2)
Running DFS (v: 7)
Running DFS (v: 8)
Running DFS (v: 10)
Did not find alternating path nor blossom
Making dual step
Tightest odd blossom (BlossomId: -1, Limit: 100000000)
Tightest even-even edge (v: 4, u: 7, Limit: 4)
Tightest even-out edge (v: 4, u: 6 Limit: 1)
Modifying dual solution (epsilon: 1)
=== Iteration state ===
Time: 11
TotalX: 5
TotalPi: 96
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 7 8 10 
Matching: (5 0) (6 3) (9 4) (12 1) (13 11) 
Pi:
0: -4
1: 3
2: 14
3: 8
4: 4
5: 4
6: 8
7: 14
8: 14
9: 2
10: 14
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 61 32 138 66 0 186 180 168 18 0 174 129 190 
61 0 33 21 31 23 69 113 167 175 59 33 0 29 
32 33 0 10 20 64 28 100 12 0 74 142 21 90 
138 21 10 0 12 100 0 64 166 164 88 110 149 68 
66 31 20 12 0 150 0 6 156 0 166 118 67 178 
0 23 64 100 150 0 84 56 18 14 126 88 105 98 
186 69 28 0 0 84 0 150 170 14 96 186 123 72 
180 113 100 64 6 56 150 0 22 48 118 40 69 112 
168 167 12 166 156 18 170 22 0 8 46 32 31 50 
18 175 0 164 0 14 14 48 8 0 140 162 21 26 
0 59 74 88 166 126 96 118 46 140 0 114 159 82 
174 33 142 110 118 88 186 40 32 162 114 0 119 0 
129 0 21 149 67 105 123 69 31 21 159 119 0 121 
190 29 90 68 178 98 72 112 50 26 82 0 121 0 
=======================
Iteration started (Time: 12)
Trying to make primal step
Running DFS (v: 2)
Running DFS (v: 7)
Running DFS (v: 8)
Running DFS (v: 10)
Did not find alternating path nor blossom
Making dual step
Tightest odd blossom (BlossomId: -1, Limit: 100000000)
Tightest even-even edge (v: 4, u: 7, Limit: 3)
Tightest even-out edge (v: 2, u: 12 Limit: 21)
Modifying dual solution (epsilon: 3)
=== Iteration state ===
Time: 12
TotalX: 5
TotalPi: 108
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 2 7 8 10 
Matching: (5 0) (6 3) (9 4) (12 1) (13 11) 
Pi:
0: -7
1: 3
2: 17
3: 11
4: 7
5: 7
6: 5
7: 17
8: 17
9: -1
10: 17
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 64 32 138 66 0 192 180 168 24 0 177 132 193 
64 0 30 18 28 20 72 110 164 178 56 33 0 29 
32 30 0 4 14 58 28 94 6 0 68 139 18 87 
138 18 4 0 6 94 0 58 160 164 82 107 146 65 
66 28 14 6 0 144 0 0 150 0 160 115 64 175 
0 20 58 94 144 0 84 50 12 14 120 85 102 95 
192 72 28 0 0 84 0 150 170 20 96 189 126 75 
180 110 94 58 0 50 150 0 16 48 112 37 66 109 
168 164 6 160 150 12 170 16 0 8 40 29 28 47 
24 178 0 164 0 14 20 48 8 0 140 165 24 29 
0 56 68 82 160 120 96 112 40 140 0 111 156 79 
177 33 139 107 115 85 189 37 29 165 111 0 119 0 
132 0 18 146 64 102 126 66 28 24 156 119 0 121 
193 29 87 65 175 95 75 109 47 29 79 0 121 0 
=======================
Iteration started (Time: 13)
Trying to make primal step
Running DFS (v: 2)
Found alternating path (v: 2, u: 7, TotalX: 5 -> 6)
! Alternating path: 
7 4 9 2
Path alternated
=== Iteration state ===
Time: 13
TotalX: 6
TotalPi: 108
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 8 10 
Matching: (5 0) (6 3) (7 4) (9 2) (12 1) (13 11) 
Pi:
0: -7
1: 3
2: 17
3: 11
4: 7
5: 7
6: 5
7: 17
8: 17
9: -1
10: 17
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 64 32 138 66 0 192 180 168 24 0 177 132 193 
64 0 30 18 28 20 72 110 164 178 56 33 0 29 
32 30 0 4 14 58 28 94 6 0 68 139 18 87 
138 18 4 0 6 94 0 58 160 164 82 107 146 65 
66 28 14 6 0 144 0 0 150 0 160 115 64 175 
0 20 58 94 144 0 84 50 12 14 120 85 102 95 
192 72 28 0 0 84 0 150 170 20 96 189 126 75 
180 110 94 58 0 50 150 0 16 48 112 37 66 109 
168 164 6 160 150 12 170 16 0 8 40 29 28 47 
24 178 0 164 0 14 20 48 8 0 140 165 24 29 
0 56 68 82 160 120 96 112 40 140 0 111 156 79 
177 33 139 107 115 85 189 37 29 165 111 0 119 0 
132 0 18 146 64 102 126 66 28 24 156 119 0 121 
193 29 87 65 175 95 75 109 47 29 79 0 121 0 
=======================
Iteration started (Time: 14)
Trying to make primal step
Running DFS (v: 8)
Running DFS (v: 10)
Did not find alternating path nor blossom
Making dual step
Tightest odd blossom (BlossomId: -1, Limit: 100000000)
Tightest even-even edge (v: 5, u: 8, Limit: 6)
Tightest even-out edge (v: 8, u: 2 Limit: 6)
Modifying dual solution (epsilon: 6)
=== Iteration state ===
Time: 14
TotalX: 6
TotalPi: 120
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 8 10 
Matching: (5 0) (6 3) (7 4) (9 2) (12 1) (13 11) 
Pi:
0: -13
1: 3
2: 17
3: 11
4: 7
5: 13
6: 5
7: 17
8: 23
9: -1
10: 23
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 70 38 144 72 0 198 186 168 30 0 183 138 199 
70 0 30 18 28 14 72 110 158 178 50 33 0 29 
38 30 0 4 14 52 28 94 0 0 62 139 18 87 
144 18 4 0 6 88 0 58 154 164 76 107 146 65 
72 28 14 6 0 138 0 0 144 0 154 115 64 175 
0 14 52 88 138 0 78 44 0 8 108 79 96 89 
198 72 28 0 0 78 0 150 164 20 90 189 126 75 
186 110 94 58 0 44 150 0 10 48 106 37 66 109 
168 158 0 154 144 0 164 10 0 2 28 23 22 41 
30 178 0 164 0 8 20 48 2 0 134 165 24 29 
0 50 62 76 154 108 90 106 28 134 0 105 150 73 
183 33 139 107 115 79 189 37 23 165 105 0 119 0 
138 0 18 146 64 96 126 66 22 24 150 119 0 121 
199 29 87 65 175 89 75 109 41 29 73 0 121 0 
=======================
Iteration started (Time: 15)
Trying to make primal step
Running DFS (v: 8)
Found alternating path (v: 8, u: 10, TotalX: 6 -> 7)
! Alternating path: 
10 0 5 8
Path alternated
=== Iteration state ===
Time: 15
TotalX: 7
TotalPi: 120
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 
Matching: (6 3) (7 4) (8 5) (9 2) (10 0) (12 1) (13 11) 
Pi:
0: -13
1: 3
2: 17
3: 11
4: 7
5: 13
6: 5
7: 17
8: 23
9: -1
10: 23
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 70 38 144 72 0 198 186 168 30 0 183 138 199 
70 0 30 18 28 14 72 110 158 178 50 33 0 29 
38 30 0 4 14 52 28 94 0 0 62 139 18 87 
144 18 4 0 6 88 0 58 154 164 76 107 146 65 
72 28 14 6 0 138 0 0 144 0 154 115 64 175 
0 14 52 88 138 0 78 44 0 8 108 79 96 89 
198 72 28 0 0 78 0 150 164 20 90 189 126 75 
186 110 94 58 0 44 150 0 10 48 106 37 66 109 
168 158 0 154 144 0 164 10 0 2 28 23 22 41 
30 178 0 164 0 8 20 48 2 0 134 165 24 29 
0 50 62 76 154 108 90 106 28 134 0 105 150 73 
183 33 139 107 115 79 189 37 23 165 105 0 119 0 
138 0 18 146 64 96 126 66 22 24 150 119 0 121 
199 29 87 65 175 89 75 109 41 29 73 0 121 0 
=======================
Alogrithm finished, de-shrinking blossoms
=== Iteration state ===
Time: 15
TotalX: 7
TotalPi: 120
Active: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 
Exposed: 
Matching: (6 3) (7 4) (8 5) (9 2) (10 0) (12 1) (13 11) 
Pi:
0: -13
1: 3
2: 17
3: 11
4: 7
5: 13
6: 5
7: 17
8: 23
9: -1
10: 23
11: 6
12: 3
13: 6
Blossoms:
AdjustedWeights:
0 70 38 144 72 0 198 186 168 30 0 183 138 199 
70 0 30 18 28 14 72 110 158 178 50 33 0 29 
38 30 0 4 14 52 28 94 0 0 62 139 18 87 
144 18 4 0 6 88 0 58 154 164 76 107 146 65 
72 28 14 6 0 138 0 0 144 0 154 115 64 175 
0 14 52 88 138 0 78 44 0 8 108 79 96 89 
198 72 28 0 0 78 0 150 164 20 90 189 126 75 
186 110 94 58 0 44 150 0 10 48 106 37 66 109 
168 158 0 154 144 0 164 10 0 2 28 23 22 41 
30 178 0 164 0 8 20 48 2 0 134 165 24 29 
0 50 62 76 154 108 90 106 28 134 0 105 150 73 
183 33 139 107 115 79 189 37 23 165 105 0 119 0 
138 0 18 146 64 96 126 66 22 24 150 119 0 121 
199 29 87 65 175 89 75 109 41 29 73 0 121 0 
=======================
