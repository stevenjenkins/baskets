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
      opts.banner = 'Usage: build_loan_sets.rb [@options] <file>'

      self[:help] = false
      opts.on( '-h', '--help', 'Display this screen' ) do
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
  puts "in = #{infile}, out = #{outfile}, exact = #{exact}"
end

class Loan
  attr_accessor :id, :amount
  def initialize(id,amount)
    @id, @amount = id, amount
  end
end

def read_data(infile)
  File.open(infile, "r") do |line|
    lid,amt,sid,minimum,maximum = line.split(',')
    if (lid != "")
      loan = Loan(lid,amt.to_i)
      @loans.append(loan)
    end
    if (sid != "")
      loanset = LoanSet(sid, minimum.to_i, maximum.to_i)
      @loan_sets.append(loanset)
    end
  end
end

def generate_output(outfile)
  File.open(outfile, "w") do |line|
    
  end
end

@loans = []
@loan_sets = []

#@arguments.each do |arg|
#handle(arg, determine_output(arg), @arguments[:exact])
  handle(@arguments[:input], determine_output(@arguments[:input]), @arguments[:exact])
#end

