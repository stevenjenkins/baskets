#!/usr/bin/env ruby
# Parse CSV files of loans and loan-sets and calculate the best sets of
# loans -- uses Minimum Subset Sum
require 'NP'
require 'optparse'

class Arguments < Hash
  attr_accessor :options 
  def initialize(args)
    super()  

    opts = OptionParser.new do |opts|
      opts.banner = 'Usage: build_loan_sets.rb [options] <file>'

      self[:help] = false
      opts.on( '-h', '--help', 'Display this screen' ) do
        self[:help] = true
        puts opts
      end

      opts.on('-i', '--input FILE', 'Name of input file') do |file|
        self[:input] = file
      end

      opts.on('-o', '--output FILE', 'Name of output file') do |file|
        self[:output] = file
      end

      self[:exact] = false
      opts.on( '-x', '--exact', 'Use exact calcualations -- slow, but use if needed') do
        self[:exact] = true
      end
    end
    opts.parse!(args)
  end
end


@arguments = Arguments.new(ARGV)

def determine_output(f)
  return 'output.csv' unless ( f || f.match('\.') )
  return @arguments[:output] if @arguments[:output]
  prefix,suffix = f.split('.')
  prefix += "-out"
  return [prefix, suffix].join('.')
end

def handle (infile,outfile,exact)
  read_data(infile)
  process_data
  write_output(outfile)
end

class Loan
  attr_accessor :id, :amount
  def initialize(id,amount)
    @id, @amount = id, amount
  end
end

class LoanSet
  attr_accessor :sid, :minimum, :maximum, :loans
  def initialize(sid,minimum,maximum)
    @sid,@minimum,@maximum = sid, minimum, maximum
    @loans = []
    self
  end
end

def read_data(infile)
  File.open(infile) do |f|
    f.each do |line|
      lid,amt,sid,minimum,maximum = line.chomp.split(',')
#puts lid,amt,sid,minimum,maximum
      if lid
       loan = Loan.new(lid.to_i,amt.to_i)
       @loans << loan
      end
      if sid
       loanset = LoanSet.new(sid.to_i, minimum.to_i, maximum.to_i)
       @loan_sets << loanset
      end
    end
  end
end

def process_data
  @loans.sort! {|a,b| a.amount <=> b.amount}
  @raw = []
  @loans.map {|loan| @raw << loan.amount }
  @raw
  @containers = []
  @loan_sets.sort! {|a,b| a.maximum <=> b.maximum}
  @loan_sets.map {|ls| @containers << ls.maximum}
  @containers.sort!
# TODO: add support for opt[:exact]
  max_set = @containers[-1]
  if max_set > 200000
    reduction_factor = max_set/200000
  else
    reduction_factor = 1
  end
  puts "using reduction factor of #{reduction_factor} as max loan set is #{max_set}"
  puts "potential profit is #{@containers.reduce(:+).to_i}"
  @raw.collect! {|loan| loan/reduction_factor}
  @containers.collect! {|maximum| maximum/reduction_factor}
  @weights = @raw.dup
  @profits = @weights.dup
  total_profit,basket_vector = NP::mulknap(@weights, @profits, @containers)
# TODO: this doesn't handle rounding correctly
  puts "profit is #{total_profit * reduction_factor}"
  puts "basket vector is #{basket_vector}"
# allocations are: [ [set, loan id, amount], ...]
  allocations = []
  basket_vector.each_with_index do |container_index,raw_index|
    allocations << [container_index, @loans[raw_index].id, @loans[raw_index].amount]
  end
  puts "allocations are #{allocations.inspect}"
  allocations.each do |allocation| 
    loanset_index,lid,amt = allocation;
# the Mulknap algorithm has '0' if the loan does not go into a set, and
# the 1-based index of the container otherwise 
    next if loanset_index == 0;
    loanset_index -= 1
#@loan_sets.index(sid).loans << Loan.new(lid,amt)
    puts "set = #{@loan_sets[loanset_index].sid}, id = #{lid}, amt = #{amt}"
    @loan_sets[loanset_index].loans << Loan.new(lid,amt)
  end
end

def write_output(outfile)
  open(outfile, 'w') do |f|
    @loan_sets.each do |ls|
      puts "Loan Set, #{ls.sid},"
      puts "Min = #{ls.minimum}, Max = #{ls.maximum}, Total = #{ls.loans.reduce {|loan| total += loan.amount}.to_i}"
      puts 'Loans,,'
      ls.loans.each do |loan|
        puts "#{loan.id}, #{loan.amount},"
      end
    end
  end
end

@loans = []
@loan_sets = []

#@arguments.each do |arg|
#handle(arg, determine_output(arg), @arguments[:exact])
  handle(@arguments[:input], determine_output(@arguments[:input]), @arguments[:exact])
#end

