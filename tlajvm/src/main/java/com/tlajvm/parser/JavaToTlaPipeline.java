package com.tlajvm.parser;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.List;

public class JavaToTlaPipeline {
    private static final Logger log = LoggerFactory.getLogger(JavaToTlaPipeline.class);
    private final Path sourceDir;
    private final Path outputDir;
    private final TlaSpecGenerator specGenerator;

    public JavaToTlaPipeline(Path sourceDir, Path outputDir) {
        this.sourceDir = sourceDir;
        this.outputDir = outputDir;
        this.specGenerator = new TlaSpecGenerator();
    }

    public void processFile(Path javaFile) throws IOException {
        log.info("Processing file: {}", javaFile);
        
        // Parse Java file
        CompilationUnit cu = StaticJavaParser.parse(javaFile);
        
        // Generate TLA+ specification
        String fileName = javaFile.getFileName().toString();
        String tlaFileName = fileName.substring(0, fileName.lastIndexOf('.')) + ".tla";
        Path tlaFile = outputDir.resolve(tlaFileName);
        log.info("Intended TLA+ output path: {}", tlaFile.toAbsolutePath());
        System.out.println("[DEBUG] Intended TLA+ output path: " + tlaFile.toAbsolutePath());
        
        // Create output directory if it doesn't exist
        Files.createDirectories(outputDir);
        
        // Generate and write TLA+ specification
        specGenerator.generateSpec(cu, tlaFile);
        log.info("Generated TLA+ specification: {}", tlaFile);
    }

    public void processDirectory() throws IOException {
        List<Path> javaFiles = new ArrayList<>();
        
        // Find all Java files in the source directory
        Files.walkFileTree(sourceDir, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                if (file.toString().endsWith(".java")) {
                    javaFiles.add(file);
                }
                return FileVisitResult.CONTINUE;
            }
        });
        
        // Process each Java file
        for (Path javaFile : javaFiles) {
            processFile(javaFile);
        }
    }

    public static void main(String[] args) {
        System.out.println("[DEBUG] JavaToTlaPipeline args: " + java.util.Arrays.toString(args));
        if (args.length < 2) {
            System.out.println("Usage: java JavaToTlaPipeline <source-dir> <output-dir>");
            System.exit(1);
        }

        try {
            Path sourceDir = Paths.get(args[0]);
            Path outputDir = Paths.get(args[1]);
            
            JavaToTlaPipeline pipeline = new JavaToTlaPipeline(sourceDir, outputDir);
            
            // If source is a file, process just that file
            if (Files.isRegularFile(sourceDir)) {
                pipeline.processFile(sourceDir);
            } else {
                // Otherwise process the directory
                pipeline.processDirectory();
            }
            
            System.out.println("TLA+ specifications generated successfully!");
        } catch (IOException e) {
            log.error("Error processing files", e);
            System.exit(1);
        }
    }
} 