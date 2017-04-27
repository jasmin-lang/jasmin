#!/usr/bin/env ruby
# watch.rb by Brett Terpstra, 2011 <http://brettterpstra.com>
# with credit to Carlo Zottmann <https://github.com/carlo/haml-sass-file-watcher>

trap("SIGINT") { exit }

if ARGV.length < 2
  puts "Usage: #{$0} watch_folder keyword"
  puts "Example: #{$0} . mywebproject"
  exit
end

dev_extension = 'dev'
filetypes = ['css','html','htm','php','rb','erb','less','js','md']
watch_folder = ARGV[0]
keyword = ARGV[1]
puts "Watching #{watch_folder} and subfolders for changes in project files..."

while true do
  files = []
  filetypes.each {|type|
    files += Dir.glob( File.join( watch_folder, "**", "*.#{type}" ) )
  }
  new_hash = files.collect {|f| [ f, File.stat(f).mtime.to_i ] }
  hash ||= new_hash
  diff_hash = new_hash - hash

  unless diff_hash.empty?
    hash = new_hash

    diff_hash.each do |df|
      if df[0].end_with?("md")
        puts "Detected change in #{df[0]}, running make doc"
        system("make doc")
      else
        puts "Detected change in #{df[0]}, refreshing"
        %x{osascript<<ENDGAME
          tell application "Google Chrome"
        	  set windowList to every window
        	  repeat with aWindow in windowList
        	  	set tabList to every tab of aWindow
          		repeat with atab in tabList
          			if (URL of atab contains "#{keyword}") then
          				tell atab to reload
          			end if
          		end repeat
          	end repeat
            # activate
          end tell
ENDGAME
}     end
    end
  end

  sleep 1
end
