package be.unamur.info.b314.compiler;

import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;

import static org.junit.Assert.*;

/**
 * Test pour vérifier la génération de code MicroPython à partir de code EMJ
 * en utilisant StringTemplate 4.
 */
public class CodeGenSTTest {

    /**
     * Test de génération de code pour un programme EMJ basique.
     * Vérifie que le code généré correspond au résultat attendu.
     */
    @Test
    public void testBasicProgramCodeGeneration() throws IOException {
        // Chemin vers le fichier EMJ de test
        String inputPath = "src/test/resources/inputs/basic_program.moj";
        
        // Chemin vers le fichier MicroPython attendu
        String expectedPath = "src/test/resources/expected/expected_basic.py";
        
        // Chemin pour le fichier de sortie généré
        String outputPath = "src/test/resources/outputs/generated_basic.py";
        
        // S'assurer que le répertoire outputs existe
        File outputDir = new File("src/test/resources/outputs");
        if (!outputDir.exists()) {
            outputDir.mkdirs();
        }
        
        // Lire le contenu du fichier MicroPython attendu
        String expectedPythonCode = new String(Files.readAllBytes(Paths.get(expectedPath)), StandardCharsets.UTF_8);
        
        // Générer le code MicroPython avec CodeGenVisitorST
        CodeGenVisitorST codeGenVisitor = new CodeGenVisitorST();
        
        // Générer le fichier de sortie
        codeGenVisitor.generateToFile(inputPath, outputPath);
        
        // Lire le fichier généré pour la comparaison
        String generatedPythonCode = new String(Files.readAllBytes(Paths.get(outputPath)), StandardCharsets.UTF_8);
        
        // Normaliser les fins de ligne pour la comparaison
        String normalizedExpected = normalizeLineEndings(expectedPythonCode);
        String normalizedGenerated = normalizeLineEndings(generatedPythonCode);
        
        // Comparer le code généré avec le code attendu
        assertEquals("Le code généré ne correspond pas au code attendu", 
                    normalizedExpected, normalizedGenerated);
    }
    
    /**
     * Normalise les fins de ligne pour la comparaison entre différents OS.
     * 
     * @param text Le texte à normaliser
     * @return Le texte avec des fins de ligne normalisées
     */
    private String normalizeLineEndings(String text) {
        return text.replaceAll("\\r\\n", "\n").replaceAll("\\r", "\n");
    }
}
