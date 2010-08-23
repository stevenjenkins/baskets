#!/usr/bin/ruby

require 'NP'
raw = [148599,241197,144000,183000,208000,125000,283000,410000,408000,299500,152800,312000,104000,410000,408000,399500,405000,395000].sort
w = [148599,241197,144000,183000,208000,125000,283000,410000,408000,299500,152800,312000,104000,410000,408000,399500,405000,395000].sort.map {|w| w/100}
p = w.dup
c = [1020000,1515000,1020000].sort.map {|c| c/100}
baskets = {}
1.upto(c.size) {|i| baskets[i] = []}

puts "raw loans = #{raw.inspect}"
#puts "loans = #{w.inspect}"
#puts "profits = #{p.inspect}"
puts "baskets = #{c.map {|item| item*100}.inspect} have a total capacity of #{c.reduce(:+) * 100}"
puts "sum of all #{p.size} loans is #{p.reduce(:+) * 100}"
a,b = NP::mulknap(w,p,c)
puts "profit is #{a * 100}"
#puts "loan allocation is #{b.inspect}"
sets = b.zip(raw)
# gives us a list of the form [[basket, amount],...]
sets.each {|pr| basket,amount = pr; if (basket != 0) then baskets[basket] << amount end}
baskets.each_key {|b| puts "Basket #{b} contains #{baskets[b].join(' ')} for a total of #{baskets[b].reduce(:+)}"}
