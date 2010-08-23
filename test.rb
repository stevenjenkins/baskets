#!/usr/bin/env ruby
require 'NP'
require 'test/unit'

class TC_NP < Test::Unit::TestCase
	def test_symmetric_subset_sum
		a,b = NP::symmetric_subset_sum([1,2,3,3],3)
		assert_equal(a, [3, 3, 3]) 
		assert_equal(b, [3, 3, 1, 2])

		a,b = NP::symmetric_subset_sum([1,2,3,4,5,6,7,8,9],3)
		assert_equal(a, [15, 15, 15])
		assert_equal(b, [3, 3, 3, 3, 3, 2, 1, 1, 2])


		a,b = NP::symmetric_subset_sum([1,2,3,4],2)
		assert_equal(a, [5, 5])
		assert_equal(b, [2, 1, 1, 2])

		a,b = NP::symmetric_subset_sum([1,2,3,4],1)
		assert_equal(a, [10])
		assert_equal(b, [1, 1, 1, 1])

		assert_nothing_raised() {
			a,b = NP::symmetric_subset_sum([],1)
		}

		a,b = NP::symmetric_subset_sum([],1)
		assert_equal(a, [])
		assert_equal(b, [])

		a,b = NP::symmetric_subset_sum([],0)
		assert_equal(a, [])
		assert_equal(b, [])

		a,b = NP::symmetric_subset_sum([7],1)
		assert_equal(a, [7])
		assert_equal(b, [1])

		assert_raise(ArgumentError) {
			a,b = NP::symmetric_subset_sum(1,1)
		}
		assert_raise(ArgumentError) {
			a,b = NP::symmetric_subset_sum(1)
		}
		assert_raise(ArgumentError) {
			a,b = NP::symmetric_subset_sum()
		}
		assert_raise(ArgumentError) {
			a,b = NP::symmetric_subset_sum([1],1,1)
		}
		assert_raise(TypeError) {
			a,b = NP::symmetric_subset_sum([1],[1])
		}

		a,b = NP::symmetric_subset_sum([34,78,21,
									   70,45,67,70,
									   19,90,76,54,
									   20,30,19,80,
									   7,65,43,56,46], 5)
		assert_equal(a, [198, 198, 198, 198, 198])

		a,b = NP::symmetric_subset_sum([34,78,21,
									   70,45,67,70,
									   19,90,76,54,
									   20,30,19,80,
									   7,65,43,56,46], 6)
		assert_equal(a, [165, 165, 165, 165, 165, 165])

		a   = NP::symmetric_subset_sum([34,78,21,
									   70,45,67,70,
									   19,90,76,54,
									   20,30,19,80,
									   7,65,43,56,46], 6)
		assert_equal(a[0], [165, 165, 165, 165, 165, 165])
	end

	def test_subset_sum
		a,b,c = NP::subset_sum([1,2,3,3],3)
		assert_equal(a, true) 
		assert_equal(b, [1, 1, 0, 0])
		assert_equal(c, 3) 

		a,b,c = NP::subset_sum([1,2,3,4,5,6,7,8,9,10],13)
		assert_equal(a, true)
		assert_equal(b, [1, 0, 0, 0, 1, 0, 1, 0, 0, 0])
		assert_equal(c, 13) 

		a,b,c = NP::subset_sum([1,2,3,4,5,6,7,8,9,10],(10*11)/2 )
		assert_equal(a, true)
		assert_equal(b, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1])
		assert_equal(c, (10*11)/2) 

		a,b,c = NP::subset_sum([1,2,3,4,5,6,7,8,9,10],(10*11 + 2)/2 )
		assert_equal(a, false)
		assert_equal(b, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1])
		assert_equal(c, (10*11)/2) 


		a,b,c = NP::subset_sum([1,2,3,4],7)
		assert_equal(a, true)
		assert_equal(b, [1, 1, 0, 1])
		assert_equal(c, 7) 

		a,b,c = NP::subset_sum([3,4,13,17], 10)
		assert_equal(a, false)
		assert_equal(b, [1, 1, 0, 0])
		assert_equal(c, 7) 

		a,b,c = NP::subset_sum([1,2,3,4],0)
		assert_equal(a, true)
		assert_equal(b, [0, 0, 0, 0])
		assert_equal(c, 0) 

		a,b,c = NP::subset_sum([1,2,3,4],-1)
		assert_equal(a, false)
		assert_equal(b, [0, 0, 0, 0])
		assert_equal(c, 0) 

		assert_nothing_raised() {
			a,b,c = NP::subset_sum([],1)
		}

		a,b,c = NP::subset_sum([],1)
		assert_equal(a, false)
		assert_equal(b, [])
		assert_equal(c, 0) 

		a,b,c = NP::subset_sum([],0)
		assert_equal(a, true)
		assert_equal(b, [])
		assert_equal(c, 0) 

		a,b,c = NP::subset_sum([7],7)
		assert_equal(a, true)
		assert_equal(b, [1])
		assert_equal(c, 7) 

		a,b,c = NP::subset_sum([7],6)
		assert_equal(a, false)
		assert_equal(b, [0])
		assert_equal(c, 0) 

		assert_raise(ArgumentError) {
			a,b,c = NP::subset_sum(1,1)
		}
		assert_raise(ArgumentError) {
			a,b,c = NP::subset_sum(1)
		}
		assert_raise(ArgumentError) {
			a,b,c = NP::subset_sum()
		}
		assert_raise(ArgumentError) {
			a,b,c = NP::subset_sum([1],1,1)
		}
		assert_raise(TypeError) {
			a,b,c = NP::subset_sum([1],[1])
		}
	end


	def test_mulknap
		assert_raise(ArgumentError) {
			a,b = NP::mulknap(1,1)
		}
		assert_raise(ArgumentError) {
			a,b = NP::mulknap(1)
		}
		assert_raise(ArgumentError) {
			a,b = NP::mulknap()
		}
		assert_raise(ArgumentError) {
			a,b = NP::mulknap([1],1,1)
		}
		assert_raise(ArgumentError) {
			a,b = NP::mulknap([1],[1])
		}
		assert_raise(ArgumentError) {
			a,b = NP::mulknap(nil)
		}
		assert_raise(ArgumentError) {
			a,b = NP::mulknap([1])
		}
		assert_raise(ArgumentError) {
			a,b = NP::mulknap([1],[1],[1],[1])
		}
		assert_raise(ArgumentError) {
			a,b = NP::mulknap([1],[1],1)
		}
		assert_raise(ArgumentError) {
			a,b = NP::mulknap(1,[1],[1])
		}
		assert_raise(ArgumentError) {
			a,b,c = NP::mulknap([1,7],[0,6],[7])
		}

		a,b,c = NP::mulknap([7],[6],[7])
		assert_equal(  6, a)
		assert_equal([1], b)

		a,b,c = NP::mulknap([1,7],[8,6],[7])
		assert_equal(  8, a)
		assert_equal([1,0], b)

		a,b,c = NP::mulknap([1,7],[1,6],[7])
		assert_equal(  6, a)
		assert_equal([0,1], b)

		a,b,c = NP::mulknap([1,7,3,4],[1,6,1,2],[2,7])
		assert_equal(  7, a)
		assert_equal([1,2,0,0], b)

		a,b,c = NP::mulknap([1,7,3,4],[1,6,1,2],[7,2])
		assert_equal(  7, a)
		assert_equal([1,2,0,0], b)

		a,b,c = NP::mulknap([1,7],[1,6],[-7])
		assert_equal(  0, a)
		assert_equal([0,0], b)
	end

end




