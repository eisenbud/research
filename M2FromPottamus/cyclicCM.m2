({1, 1, 1}, {1, 3, 3, 1}) -- koszul	
({1, 2, 1}, {1, 2, 2, 1}) -- double is the generic module; this one doesn't exist

({2, 1, 1}, {1, 6, 8, 3}) -- Eagon Northcott (square of max ideal)
({2, 1, 2}, {1, 5, 5, 1}) -- Linear 5x5 Pfaffian

({3, 1, 1}, {1, 10, 15, 6}) --cube of max ideal
({3, 1, 2}, {1, 8, 9, 2}) -- 8 general cubics
({3, 1, 3}, {1, 7, 7, 1}) -- Pfaffian
({3, 2, 1}, {1, 5, 9, 5}) -- 5 generic cubics
({3, 2, 3}, {1, 4, 4, 1}) -- doesn't exist, but the double does (testGeneric(D,2))

({4, 1, 1}, {1, 15, 24, 10}) -- 4th power of max ideal
({4, 1, 4}, {1, 9, 9, 1}) -- Pfaffian
({4, 2, 1}, {1, 7, 14, 8}) -- 7 general 4-ics or testGeneric

({4, 5, 1}, {1, 3, 8, 6})  --- does NOT exist (would be reg seq). 
-- over a field with 2,3, or 5 elements, 2 times this is ok

({5, 1, 1}, {1, 21, 35, 15}) -- 5th power of max ideal
({5, 1, 2}, {1, 16, 20, 5}) -- 16 general qpuintics OR testGeneric
({5, 1, 5}, {1, 11, 11, 1}) -- Pfaffian
({5, 2, 5}, {1, 6, 6, 1})   -- doesn't exist, but double does from testGeneric
({5, 3, 1}, {1, 6, 15, 10}) -- generic forms

({6, 1, 1}, {1, 28, 48, 21}) -- 6th power of max ideal
({6, 1, 2}, {1, 21, 27, 7}) -- generic forms
({6, 1, 6}, {1, 13, 13, 1}) -- Pfaffian
({6, 2, 1}, {1, 12, 27, 16}) -- generic forms

({7, 1, 1}, {1, 36, 63, 28}) -- power of max id
({7, 1, 7}, {1, 15, 15, 1})  -- pfaffian
({7, 2, 1}, {1, 15, 35, 21}) -- generic forms
({7, 2, 7}, {1, 8, 8, 1})   -- doesn't exist, but twice it does (testGeneric)
({7, 3, 2}, {1, 8, 14, 7}) -- generic forms

({8, 1, 1}, {1, 45, 80, 36}) -- power of the max ideal
o({8, 1, 2}, {1, 33, 44, 12}) -- generic forms
({8, 1, 3}, {1, 27, 32, 6})  -- generic forms
({8, 1, 8}, {1, 17, 17, 1})  -- Pfaffian
({8, 3, 1}, {1, 11, 32, 22}) -- generic forms
({8, 6, 1}, {1, 5, 20, 16}) -- testSocle

({9, 1, 1}, {1, 55, 99, 45})-- power of the max ideal
({9, 1, 2}, {1, 40, 54, 15}) -- generic forms
({9, 1, 5}, {1, 25, 27, 3}) -- testSocle
({9, 1, 9}, {1, 19, 19, 1}) -- Pfaffian
({9, 2, 1}, {1, 22, 54, 33}) --generic
({9, 2, 9}, {1, 10, 10, 1}) --testSocle 2
({9, 3, 1}, {1, 13, 39, 27}) -- generic (not testSocle)
({9, 5, 1}, {1, 7, 27, 21}) -- testSocle

({10, 1, 1}, {1, 66, 120, 55})-- power of the max ideal
({10, 1, 10}, {1, 21, 21, 1}) -- Pfaffian
({10, 2, 1}, {1, 26, 65, 40}) -- generic
({10, 2, 3}, {1, 18, 25, 8})  -- generic (not socle)
({10, 3, 2}, {1, 13, 25, 13}) -- socle
({10, 5, 1}, {1, 8, 32, 25})  -- socle


The following are all the examples in 
3 variables up to deg shift 
E=(20, 20, 20) where neither of the
obvious construction methods works.
We know the 1,2n,2n,1 are impossible,
but become possible when doubled. (proof??)

({1, 2, 1}, {1, 2, 2, 1})
({3, 2, 3}, {1, 4, 4, 1})
({4, 5, 1}, {1, 3, 8, 6}) --
({5, 2, 5}, {1, 6, 6, 1})
({6, 14, 1}, {1, 2, 9, 8}) --
({7, 2, 7}, {1, 8, 8, 1})
({9, 2, 9}, {1, 10, 10, 1})
({11, 2, 11}, {1, 12, 12, 1})
({13, 2, 13}, {1, 14, 14, 1})
({15, 2, 15}, {1, 16, 16, 1})
({15, 20, 1}, {1, 3, 27, 25}) --
({17, 2, 17}, {1, 18, 18, 1})
({17, 4, 3}, {1, 18, 34, 17}) --
({18, 7, 3}, {1, 10, 24, 15}) --
({19, 2, 19}, {1, 20, 20, 1})
