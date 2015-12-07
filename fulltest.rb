# coding: utf-8

require "open3"

STATIC_SEM_DIR = 'static'
STATIC_SEM_FILE = 'k-metaml-typing.k'

DYNAMIC_SEM_DIR = 'dynamic'
DYNAMIC_SEM_FILE = 'k-metaml-exec.k'

TEST_DIR = 'test'

#
def build(path, name)
  puts "kompiling #{name} ..."

  Dir.chdir(path) do
    unless system("kompile #{name}")
      raise "failed to kompile #{name} at #{path}"
    end
  end

  puts "complete!"
end

def glob_code_filenames(path)
  Dir.chdir(path) do
    return Dir.glob("*.a")
  end
end

def make_option_string(options)
  return options.map{|k, v| "#{k} #{if v.nil? then '' else v end}" }.join(' ')
end

def auto_generate_testcase(filename, result)
  File.write(filename, result)
end

# return: nil => Passed, String => Failed(error messages)
def check_result(filename, result, must_fail, tag)
  if must_fail && !result.match(/^No search results$/)
    s = ""
    s << "This case must be failed (type unsafe)\n"

    return s
  end

  if File.exists?(filename)
    content = File.read(filename)
    if result != content
      s = ""
      s << "===== expect:\n"
      s << content
      s << "\n"
      s << "===== actual:\n"
      s << result
      s << "\n"
      s << "====="

      return s
    else
      return nil
    end

  else
    if result.length > 0
      puts "[!] WARNING: no test for #{tag} (#{filename}) ===== "

      # auto_generate_testcase(filename, result)

      puts result
      puts "    " + "=" * 20
    end

    return nil
  end
end

def run_tests(test_dir, sem_dir, test_io_dir, filenames, fail_cases, is_dynamic, options = {})
  ops = make_option_string(options)
  num_of_tests = filenames.length

  Dir.chdir(sem_dir) do
    return filenames.map.with_index do |fname, index|
      must_fail = fail_cases.include?(fname)

      abs_source_path = File.join(test_dir, fname)

      # abs_test_in = File.join(test_io_dir, "#{fname}.in")
      abs_test_out = File.join(test_io_dir, "#{fname}.out")
      abs_test_err = File.join(test_io_dir, "#{fname}.err")

      puts "[ ] " + "-" * 40
      puts "[+] Running '#{abs_source_path}' (at #{sem_dir}) [#{index+1}/#{num_of_tests}]"
      if must_fail
        puts "[!] fail case"
      end
      puts "[ ] " + "-" * 40

      if is_dynamic && must_fail
        puts "[o] SKIPPED: (type unsafe)"
        next nil
      end

      o, e, s = Open3.capture3("krun --search --debug #{ops} #{abs_source_path}")
      exec_err = nil
      if s.exitstatus != 0
        # ...
        p s

        exec_err = s
      end

      outres = check_result(abs_test_out, o, must_fail, 'stdout')
      if outres.nil?
        puts "[o] PASS: (stdout)"
      else
        puts "[x] FAIL: (stdout)"
        puts outres
      end

      errres = check_result(abs_test_err, e, false, 'stderr')
      if errres.nil?
        puts "[o] PASS: (stderr)"
      else
        puts "[x] FAIL: (stderr)"
        puts errres
      end

      if !exec_err.nil? || !outres.nil? || !errres.nil?
        # case failed
        next {
          exec_err: exec_err,
          outres: outres,
          errres: errres,
        }

      else
        # case passed
        next nil
      end
    end
  end
end

def run_test(
      static_rel_dir,
      static_fname,
      dynamic_rel_dir,
      dynamic_fname,
      test_rel_dir
    )
  abs_static_sem_dir = File.expand_path(static_rel_dir, File.dirname(__FILE__))
  abs_dynamic_sem_dir = File.expand_path(dynamic_rel_dir, File.dirname(__FILE__))

  abs_test_dir = File.expand_path(test_rel_dir, File.dirname(__FILE__))
  abs_static_test_dir = File.join(abs_test_dir, static_rel_dir)
  abs_dynamic_test_dir = File.join(abs_test_dir, dynamic_rel_dir)

  fail_cases = File.read(File.join(abs_test_dir, "fail_cases.list")).split("\n")

  # run kompile
  #build(abs_static_sem_dir, static_fname)
  #build(abs_dynamic_sem_dir, dynamic_fname)

  # filenames
  fns = glob_code_filenames(abs_test_dir)

  # run tests
  puts ""
  puts "STATIC"
  puts ""
  st = run_tests(abs_test_dir, abs_static_sem_dir, abs_static_test_dir, fns, fail_cases, false, {
                   '--symbolic-execution' => nil,
                   '--pattern' => "'<k> V:Type </k> <level> N:Int </level>'"
                 })

  st_s = st.count{|e| e.nil? }
  st_f = st.size - st_s
  puts ""
  puts "|| static PASSED(#{st_s}) / FAILED(#{st_f})"
  puts "=" * 60

  puts ""
  puts "DYNAMIC"
  puts ""
  rt = run_tests(abs_test_dir, abs_dynamic_sem_dir, abs_dynamic_test_dir, fns, fail_cases, true, {
                   '-c' => "VENV='.Map'",
                   '--pattern' => "'<k> V:Term </k> <level> N:Int </level>'"
                 })

  rt_s = rt.count{|e| e.nil? }
  rt_f = rt.size - rt_s
  puts ""
  puts "|| dynamic PASSED(#{rt_s}) / FAILED(#{rt_f})"
  puts "=" * 60

  if st_f != 0 || rt_f != 0
    exit -1
  end
end

#
run_test(
  STATIC_SEM_DIR,
  STATIC_SEM_FILE,
  DYNAMIC_SEM_DIR,
  DYNAMIC_SEM_FILE,
  TEST_DIR
)
