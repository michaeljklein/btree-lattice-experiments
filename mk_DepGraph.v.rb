#!/usr/bin/env ruby

require 'fileutils'

# $ /usr/bin/env ruby --version
# ruby 2.7.1p83 (2020-03-31 revision a0c7c23c9c) [x86_64-darwin19]

/mk_(?<coq_module_name>\w+)\.v\.rb$/ =~ __FILE__

puts "Generating #{coq_module_name}.v"

# collect coq module names
coq_project_files = File.readlines('_CoqProject').map(&:chomp).reject do |x|
  # - empty lines
  # - command line arguments
  # - comments
  # - DepGraph.v itself
  # - AxiomFinder.v
  # - Theory.v
  x.match? /(^$|^[-#]|#{coq_module_name}.v|AxiomFinder.v|Theory.v$)/
end.map do |x|
  x.sub(/\.v$/, '').tr '/', '.'
end.to_a

# write temp coq module
File.open("#{coq_module_name}.v.temp", 'w') do |f|
  f.puts '(* DO NOT MODIFY *)'
  f.puts "(* #{coq_module_name}.v is generated by mk_#{coq_module_name}.v.rb *)"
  f.puts "(* Run ./mk_#{coq_module_name}.v.rb to regenerate *)"
  f.puts
  f.puts 'Require dpdgraph.dpdgraph.'
  coq_project_files.each do |coq_project_file|
    f.puts "From Embed Require #{coq_project_file}."
  end
  f.puts
  f.puts "Print FileDependGraph #{coq_project_files.join ' '}."
  f.puts
end

# update by overwriting or delete the temp module
if File.exist?("#{coq_module_name}.v")
  if File.read("#{coq_module_name}.v") == ("#{coq_module_name}.v.temp")
    FileUtils.rm "#{coq_module_name}.v.temp"
  else
    FileUtils.mv "#{coq_module_name}.v.temp", "#{coq_module_name}.v"
  end
else
  FileUtils.mv "#{coq_module_name}.v.temp", "#{coq_module_name}.v"
end

puts "Generated #{coq_module_name}.v"

