/*
 * Copyright 2017-2019 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package ru.ispras.microtesk.model.riscv;

import org.apache.commons.lang.StringUtils;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;

import ru.ispras.castle.util.FileUtils;
import ru.ispras.castle.util.Logger;
import ru.ispras.castle.util.Logger.EventType;
import ru.ispras.microtesk.options.Option;
import ru.ispras.microtesk.test.Statistics;
import ru.ispras.microtesk.test.testutils.TemplateTest;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

public class RiscVTest extends TemplateTest {

  /**
   * Test execution phases enumeration.
   */
  public enum TestPhase {
    PROGRAM_GENERATION,
    COMPILATION,
    EMULATION,
    CHECK_TRACES,
    NONE
  }

  /**
   * The execution phase at which the test is allowed to fail.
   */
  private TestPhase failPhase;

  /**
   * The current phase of test execution.
   */
  private TestPhase currentPhase;

  /**
   * Shows whether rest of test execution phases should be skipped for the current test program.
   */
  private boolean skipRestPhases;

  /**
   * The test program name prefix.
   */
  private String programPrefix;

  /**
   * The path to directory containing test program.
   */
  private String testDirPath;

  /**
   * Path to test results.
   */
  private static final String TEST_PATH = System.getenv("TEST_PATH");

  /**
   * Shell interpreter.
   */
  private static final File SHELL = new File(System.getenv("SHELL"));

  /**
   * Test programs extension.
   */
  private static final String EXT = "s";

  /* Toolchain parameters. */

  /**
   * RISC-V toolchain path environment variable name.
   */
  private static final String RISCV_TCHAIN_PATH = "RISCV_TCHAIN";

  /**
   * RISC-V toolchain path environment variable.
   */
  private static final String TCHAIN_PATH = System.getenv(RISCV_TCHAIN_PATH);

  /**
   * RISC-V Linux GNU toolchain components common prefix.
   */
  private static final String TCHAIN_PREFIX = "riscv64-unknown-linux-gnu";

  private static final String LINKER_SCRIPT_EXT = "ld";

  /* QEMU for RISC-V parameters. */

  /**
   * QEMU binary name.
   */
  private static final String QEMU_BIN = "qemu-system-riscv64";

  /**
   * QEMU location environment variable name.
   */
  private static final String QEMU_VAR = "QEMU_RISCV_PATH";

  /**
   * QEMU location environment variable.
   */
  private static final String QEMU_PATH = System.getenv(QEMU_VAR);

  /**
   * Timeout for QEMU execution (in milliseconds).
   */
  private static final int QEMU_TIMEOUT_MILLIS = 1000;

  /* Spike parameters. */

  /**
   * Spike binary name.
   */
  private static final String SPIKE_BIN = "spike";

  /**
   * Timeout for Spike execution (in seconds).
   */
  private static final int SPIKE_TIMEOUT_SEC = 1;

  /* Trace utils parameters. */

  /**
   * Trace utils binary name.
   */
  private static final String TRACE_BIN = "traceutils";

  /**
   * Trace utils location environment variable name.
   */
  private static final String TRACE_VAR = "TRACE_PATH";

  /**
   * Trace utils location environment variable.
   */
  private static final String TRACE_PATH = System.getenv(TRACE_VAR);

  /**
   * Trace utils main binary file.
   */
  private static final File TRACER = new File(String.format("%s/%s",TRACE_PATH, TRACE_BIN));

  /**
   * Tracer matching window size (in ticks).
   */
  private static final String TRACER_WINDOW_SIZE = "5";

  /**
   * Revision identifier.
   */
  private static final String RISCV_REV = "RV64FULL";

  /**
   * Default constructor.
   */
  public RiscVTest() {
    super(
        "riscv",
        "build/target/arch/riscv/templates"
        );
    failOnPhase(TestPhase.NONE);
  }

  @Override
  public void onEventLogged(final EventType type, final String message) {
    if (EventType.ERROR == type || EventType.WARNING == type || message.startsWith("Error")) {
      if (!isExpectedError(message)) {
        Assert.fail(message);
      }
    }
  }

  protected boolean isExpectedError(final String message) {
    return message.contains("Exception handler for TLBMiss is not found")
           || message.contains("Exception handler for TLBInvalid is not found")
           || message.contains(
           "Warning: Failed to load the MMU model. Physical memory will be accessed directly.");

  }

  @Override
  public Statistics run(final String file) {
    setProgramPrefix(file);

    final String fileDir = FileUtils.getFileDir(file);
    final Path testDirPath = null != fileDir ? Paths.get(TEST_PATH, fileDir, getProgramPrefix())
                                             : Paths.get(TEST_PATH, getProgramPrefix());
    setTestDirPath(testDirPath);

    setCommandLineOption(Option.TRACER_LOG);
    setCommandLineOption(Option.COVERAGE_LOG);
    setCommandLineOption(Option.OUTPUT_DIR, getTestDirPath());
    setCommandLineOption(Option.CODE_FILE_EXTENSION, EXT);
    setCommandLineOption(Option.DATA_FILE_EXTENSION, EXT);
    setCommandLineOption(Option.REV_ID, RISCV_REV);
    return super.run(file);
  }

  private void setProgramPrefix(final String file) {
    this.programPrefix = FileUtils.getShortFileNameNoExt(file);
  }

  private void setTestDirPath(final Path testDirPath) {
    this.testDirPath = testDirPath.toString();
  }

  private String getProgramPrefix() {
    return programPrefix;
  }

  private String getTestDirPath() {
    return testDirPath;
  }

  /**
   * Sets the specified execution phase at which this test is allowed to fail.
   * @param phase The test execution phase at which it's allowed to fail.
   */
  protected void failOnPhase(final TestPhase phase) {
    this.failPhase = phase;
  }

  private void setPhase(final TestPhase phase) {
    this.currentPhase = phase;
  }

  private boolean canFailOnCurrentPhase() {
    return this.currentPhase == this.failPhase;
  }

  private void skipRestPhases(final boolean skipRestPhases) {
    this.skipRestPhases = skipRestPhases;
  }

  private boolean skippedPhase() {
    return skipRestPhases;
  }

  /**
   * Sets test parameters.
   */
  @Before
  public void setUp() {
    setPhase(TestPhase.PROGRAM_GENERATION);
  }

  /**
   * Compiles generated test programs and runs them on emulator.
   */
  @After
  public void compileAndEmulate() {

    if (canFailOnCurrentPhase()) {

      /* No test programs are generated by this test, finish it. */
      return;
    }

    /* Check whether toolchain has been installed. */

    if (TCHAIN_PATH == null || TCHAIN_PATH.isEmpty()) {
      Assert.fail(
          String.format("Can't find toolchain: '%s' env var points to null!", RISCV_TCHAIN_PATH));
      return;
    }

    final File compiler = getToolchainBinary();

    /* If toolchain is installed, loop on prefix-named test programs,
     * compile every test program, if it fails, throw error message. */
    final File testDir = new File(getTestDirPath());

    if (!testDir.exists() || !testDir.isDirectory()) {
      Assert.fail(String.format("Can't find '%s' test program directory.", getTestDirPath()));
    }

    final File[] files = testDir.listFiles();

    final Collection<File> auxFiles = new LinkedHashSet<>();
    final Collection<File> tests = new LinkedHashSet<>();

    Assert.assertNotNull("No test programs are generated from this template.", files);

    for (final File file : files) {

      final String fileName = file.getName();
      if (fileName.endsWith(EXT)) {
        if (fileName.startsWith(getProgramPrefix())) {
          tests.add(file);
        } else {
          auxFiles.add(file);
        }
      }
    }

    for (final File program : tests) {
      skipRestPhases(false);
      final File image = compile(program, auxFiles, compiler);
      emulate(image);
    }
  }

  private void emulate(final File image) {

    Logger.message("Start simulation on Spike ...");

    /* Check if Spike is installed. */
    checkExecutable(new File(String.format("%s/bin/%s", TCHAIN_PATH, SPIKE_BIN)));

    final String spikeLog = insertExt(image.getAbsolutePath(), "-spike.log");
    final String spikeRunScript =
        Paths.get(System.getenv("MICROTESK_HOME"), "bash", "run-on-spike.sh").toString();

    final String[] shellSpikeArgs = new String[] {
        "-c", String.format("%s %s %d %s",
        spikeRunScript,
        image.getAbsolutePath(),
        SPIKE_TIMEOUT_SEC,
        spikeLog)};

    final Collection<Integer> spikeRetValues = new LinkedList<>();
    spikeRetValues.add(0);
    spikeRetValues.add(156); // to mask "killed by test" situation

    runShell(spikeRetValues, shellSpikeArgs);
    final File spikeLogFile = new File(spikeLog);

    Assert.assertTrue(
        String.format("Can't find Spike trace file: %s", spikeLogFile.getAbsolutePath()),
        spikeLogFile.exists());

    Logger.message("done.");

    /* If QEMU is installed, run the binary image on it. */

    if (QEMU_PATH == null || QEMU_PATH.isEmpty()) {
      Assert.fail(
          String.format(
              "Can't find emulator: '%s' env var doesn't point to '%s' binary.",
              QEMU_VAR,
              QEMU_BIN));
      return;
    }

    final File qemu = new File(String.format("%s/%s", QEMU_PATH, QEMU_BIN));
    checkExecutable(qemu);

    Logger.message("Start simulation on QEMU ...");
    setPhase(TestPhase.EMULATION);
    final String qemuLog = insertExt(image.getAbsolutePath(), "-qemu.log");

    final String[] qemuArgs = new String[] {
        "-M",
        "spike",
        "-cpu",
        "any",
        "-d",
        "unimp,nochain,in_asm",
        "-nographic",
        "-singlestep",
        "-trace-log",
        "-D",
        qemuLog,
        "-bios",
        image.getAbsolutePath()};
    runQemu(qemu, qemuArgs);

    final File qemuLogFile = new File(qemuLog);
    Assert.assertTrue(
        String.format("Can't find QEMU trace file: %s", qemuLogFile.getAbsolutePath()),
        qemuLogFile.exists());

    Logger.message("done.");

    Logger.message("Check traces ...");
    setPhase(TestPhase.CHECK_TRACES);

    final File toolLog = new File(insertExt(image.getAbsolutePath(), ".log"));

    Assert.assertTrue(
        String.format("Can't find MicroTESK Tracer log file: %s", toolLog.getAbsolutePath()),
        toolLog.exists());

    /* Use Trace Matcher for logs comparison. */
    checkExecutable(TRACER);

    final String [] args = new String [] {
        "-c",
        String.format("%s %s %s %s %s > %s",
            TRACER.getAbsolutePath(),
            "--window-size " + TRACER_WINDOW_SIZE,
            "--first-dif-stop",
            toolLog.getAbsolutePath(),
            qemuLogFile.getAbsolutePath(),
            compareResultFileName(toolLog, qemuLogFile))};
    final Collection<Integer> diffReturnValues = new LinkedList<>();
    diffReturnValues.add(0);
    diffReturnValues.add(1); // to mask "files are not equal" situation

    runShell(diffReturnValues, args);

    Logger.message("done.");
  }

  private static String compareResultFileName(final File first, final File second) {
    return String.format(
        "%s/%s-vs-%s.txt",
        FileUtils.getFileDir(first.getAbsolutePath()),
        FileUtils.getShortFileNameNoExt(first.getName()),
        FileUtils.getShortFileNameNoExt(second.getName()));
  }

  private File compile(
      final File program,
      final Collection<File> auxFiles,
      final File compiler) {

    Logger.message(String.format("Start compilation of %s ...", program.getName()));
    setPhase(TestPhase.COMPILATION);

    final List<String> args = new LinkedList<>();
    args.add(program.getAbsolutePath());

    for (final File auxFile : auxFiles) {
      args.add(auxFile.getAbsolutePath());
    }
    args.add("-march=rv64gcv");
    args.add("-nostdlib");
    args.add("-nostartfiles");
    final String linkerScriptPath = getLinkerScript(new File(getTestDirPath()));

    if (linkerScriptPath.length() > 0) {
      args.add(String.format("-T%s", linkerScriptPath));
    } else {

      args.add("-Ttext");
      args.add("0x1000");
    }
    args.add("-o");
    args.add(getOutElf(getNameNoExt(program)));

    runCommand(
        compiler, args.toArray(new String[0]));

    final File elfImage = new File(getElf(program));

    Logger.message("done.");
    return elfImage;
  }

  private String getLinkerScript(final File testDirPath) {

    String path = "";

    final File[] files = testDirPath.listFiles();

    Assert.assertNotNull("No test programs are generated from this template.", files);

    for (final File file : files) {

      final String fileName = file.getName();

      if (fileName.endsWith(LINKER_SCRIPT_EXT)) {

        path = file.getPath();
        break;
      }
    }

    return path;
  }

  private String getElf(final File program) {
    final String[] elfFiles = getElfFiles(program);
    return elfFiles[0];
  }

  private String[] getElfFiles(final File... files) {

    final String[] result = new String[files.length];

    for (int i = 0; i < files.length; i++) {
      final File file = files[i];
      final String pathWithExt = insertExt(file.getAbsolutePath(), ".elf");

      final File fileWithExt = new File(pathWithExt);
      if (!fileWithExt.exists() || fileWithExt.isDirectory()) {
        Assert.fail(String.format("Can't find: %s", pathWithExt));
      }
      result[i] = fileWithExt.getAbsolutePath();
    }

    return result;
  }

  private static String insertExt(final String path, final String ext) {
    return String.format(
        "%s%s",
        path.substring(0, path.contains(".") ? path.lastIndexOf('.') : path.length()),
        ext);
  }

  private void runCommand(final File cmd, final String... args) {
    runCommand(cmd, 0, true, Collections.singletonList(0), args);
  }

  private void runQemu(final File cmd, final String... args) {
    runCommand(cmd, RiscVTest.QEMU_TIMEOUT_MILLIS, true, Collections.singletonList(0), args);
  }

  private void runShell(final Collection<Integer> returnValues, final String... args) {

    runCommand(RiscVTest.SHELL, 0, false, returnValues, args);
  }

  private void runCommand(
      final File cmd,
      final long timeout,
      final boolean redirectError,
      final Collection<Integer> returnCodes,
      final String ... args) {

    if (skippedPhase()) {
      return;
    }

    final String[] cmdArray = toArray(cmd, args);
    final String command = StringUtils.join(cmdArray, ' ');

    try {
      final ProcessBuilder builder = new ProcessBuilder(cmdArray);
      final File errorLog = new File(getTestDirPath() + "/error-log.txt");
      if (redirectError) {
        builder.redirectError(errorLog);
      }
      final Process process = builder.start();

      int exitCode;

      if (timeout > 0) {

        Thread.sleep(timeout);

        try {
          exitCode = process.exitValue();

        } catch (IllegalThreadStateException e) {

          Logger.message("Timeout is expired for: \"%s\"", command);
          exitCode = 0;

        } finally {
          process.destroyForcibly();
        }
      } else {
        exitCode = process.waitFor();
        process.destroyForcibly();
      }

      if (!returnCodes.contains(exitCode) || !isEmpty(errorLog)) {

        if (canFailOnCurrentPhase()) {

          /* It is planned for test to fail on this phase, finish with success.
           * The finishing is treated as skipping of the rest of test execution phases. */
          skipRestPhases(true);
          return;
        }

        if (isEmpty(errorLog)) {

          final String returnMsg =
              String.format("Process has returned '%d': \"%s\"%n", exitCode, command);
          final String logMsg =
              String.format("No error log is found, try to run command in terminal.%n");
          Assert.fail(returnMsg + logMsg);
        }

        final byte [] errLogBytes = Files.readAllBytes(Paths.get(errorLog.getPath()));
        final String errString = new String(errLogBytes, Charset.defaultCharset());

        final String qemuTerminateHeader = "qemu-system-riscv64: terminating on signal";

        if (!errString.startsWith(qemuTerminateHeader) && !returnCodes.contains(exitCode)) {

          final String returnMsg =
              String.format("Process has returned '%d': \"%s\"%n", exitCode, command);
          String logMsg;
          if (errString.length() > 0) {
            logMsg = String.format("Error log is:%n %s%n", errString);
          } else {
            logMsg = String.format("No error log is found, try to run command in terminal.%n");
          }
          Assert.fail(returnMsg + logMsg);
        }
      }
      if (errorLog.exists() && !errorLog.delete()) {
        Assert.fail("Can't delete error log file: " + errorLog.getAbsolutePath());
      }
    } catch (final IOException | InterruptedException e) {
      e.printStackTrace();
      Assert.fail(e.getMessage());
    }
  }

  private String[] toArray(
      final File command,
      final String ... args) {

    final List<String> commands = new LinkedList<>();
    commands.add(command.getAbsolutePath());
    Collections.addAll(commands, args);

    return commands.toArray(new String[0]);
  }

  private String getOutElf(final String fileNamePrefix) {

    return String.format("%s/%s.elf", getTestDirPath(), fileNamePrefix);
  }

  private static String getNameNoExt(final File file) {
    return FileUtils.getShortFileNameNoExt(file.getName());
  }

  private static File getToolchainBinary() {

    final String fullPath = String.format("%s/bin/%s-gcc", TCHAIN_PATH, TCHAIN_PREFIX);
    final File binary = new File(fullPath);

    checkExecutable(binary);
    return binary;
  }

  private static void checkExecutable(final File file) {

    Assert.assertTrue(String.format("Can't find: %s", file.getAbsolutePath()), isExecutable(file));
  }

  private static boolean isExecutable(final File file) {
    return file.exists() && !file.isDirectory() && file.canExecute();
  }

  private static boolean isEmpty(final File file) {

    if (!file.exists()) {
      return true;
    }
    try {
      final BufferedReader reader =
          new BufferedReader(
              new InputStreamReader(new FileInputStream(file), Charset.defaultCharset()));

      final String firstLine = reader.readLine();
      reader.close();
      return firstLine == null;

    } catch (final IOException e) {
      e.printStackTrace();
      Assert.fail(e.getMessage());
    }
    return false;
  }
}
