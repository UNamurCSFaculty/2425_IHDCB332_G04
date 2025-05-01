package be.unamur.info.b314.compiler.main;

import be.unamur.info.b314.compiler.emj.EMJSymbolTable;
import be.unamur.info.b314.compiler.emj.EMJSymbolInfo;
import be.unamur.info.b314.compiler.emj.EMJParameterInfo;
import org.junit.Test;
import org.junit.Rule;
import org.junit.rules.TemporaryFolder;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

/**
 * Tests pour la table des symboles EMJ
 * 
 * Ce test vérifie le bon fonctionnement de la méthode displaySymbolTable()
 */
public class EMJSymbolTableTest {
    
    private static final Logger logger = LoggerFactory.getLogger(EMJSymbolTableTest.class);
    
    @Rule
    public TemporaryFolder testFolder = new TemporaryFolder(); // Crée un dossier temporaire pour les tests
    
    @Rule
    public TestRule watcher = new TestWatcher() {
        @Override
        protected void starting(Description description) {
            logger.info(String.format("Starting test: %s()...",
                    description.getMethodName()));
        }
    };
    
    @Test
    public void testSymbolTableDisplay() throws Exception {
        // Créer une instance de EMJSymbolTable
        EMJSymbolTable symbolTable = new EMJSymbolTable();
        
        // ---- VARIABLES GLOBALES ----
        // Variables numériques (utilisation de 🔢 pour INT)
        symbolTable.addVariable("👌", "INT", true);       // emoji OK vu dans les exemples
        symbolTable.addVariable("compteur", "INT", true);
        symbolTable.addVariable("🎮", "INT", false);      // emoji manette (vu dans les tests)
        
        // Variables textuelles (utilisation de 🔡 pour STRING)
        symbolTable.addVariable("message", "STRING", true);
        symbolTable.addVariable("🦅", "STRING", false);   // emoji aigle (vu dans les tests)
        
        // Variables booléennes (utilisation de 🔚 pour BOOL)
        symbolTable.addVariable("estActif", "BOOL", true);
        symbolTable.addVariable("🍌", "BOOL", false);     // emoji banane (vu dans les tests)
        
        // Tableaux (utilisation de 📚 pour les tableaux)
        symbolTable.addVariable("tableauTest", "INT[]", true);
        
        // ---- FONCTIONS ----
        // Fonction main (toujours présente dans EMJ avec emoji 🏠)
        symbolTable.addFunction("🏠", "VOID", new ArrayList<>());

        // Fonction void avec l'emoji 🌀 (vu dans les exemples)
        List<EMJParameterInfo> params1 = new ArrayList<>();
        symbolTable.addFunction("🌀", "VOID", params1);
        
        // Fonction de déplacement (emoji ⬆️ - flèche vers le haut)
        List<EMJParameterInfo> directionParams = new ArrayList<>();
        directionParams.add(new EMJParameterInfo("steps", "INT"));
        symbolTable.addFunction("⬆️", "VOID", directionParams);
        
        // Fonction de calcul avec retour d'entier
        List<EMJParameterInfo> calcParams = new ArrayList<>();
        calcParams.add(new EMJParameterInfo("a", "INT"));
        calcParams.add(new EMJParameterInfo("b", "INT"));
        symbolTable.addFunction("calculerSomme", "INT", calcParams);
        
        // Fonction d'affichage sans paramètres (attendue par les assertions)
        symbolTable.addFunction("afficherMessage", "VOID", new ArrayList<>());
        
        // ---- PORTÉES LOCALES ----
        // Portée de boucle (utilisation de 🔂 pour les boucles, vu dans les tests)
        symbolTable.enterScope("loop");
        symbolTable.addVariable("i", "INT", true);          // variable d'itération classique
        symbolTable.addVariable("compteurBoucle", "INT", true);  // compteur dans la boucle
        
        // Portée conditionnelle dans la boucle (⤴️ pour les conditions)
        symbolTable.enterScope("if");
        symbolTable.addVariable("etatValeur", "STRING", true);   // variable dans condition
        
        // Remonter à la portée de la boucle
        symbolTable.exitScope();  // sortir de "if"
        
        // Créer une autre portée de fonction
        symbolTable.exitScope();  // sortir de "loop"
        symbolTable.enterScope("afficherResultat");
        symbolTable.addVariable("temp", "INT", true);         // variable locale fonction
        symbolTable.addVariable("resultatMessage", "STRING", true); // variable locale
        
        // Rediriger System.out pour capturer la sortie
        ByteArrayOutputStream outContent = new ByteArrayOutputStream();
        PrintStream originalOut = System.out;
        System.setOut(new PrintStream(outContent));
        
        try {
            // Appel de la fonction à tester pour capturer la sortie
            symbolTable.displaySymbolTable();
            
            // Récupérer la sortie capturée
            String output = outContent.toString();
            
            // Restaurer temporairement System.out pour afficher la table des symboles
            System.setOut(originalOut);
            System.out.println("\n******** AFFICHAGE DE LA TABLE DES SYMBOLES DURANT LE TEST ********");
            symbolTable.displaySymbolTable();
            System.out.println("******** FIN DE L'AFFICHAGE DE TEST ********\n");
            
            // Remettre le flux de capture pour la suite du test
            System.setOut(new PrintStream(outContent));
            
            // Vérifier que la sortie contient les noms des variables et fonctions
            assertTrue("La sortie devrait contenir la variable 'compteur'", 
                    output.contains("compteur"));
            assertTrue("La sortie devrait contenir la variable 'message'", 
                    output.contains("message"));
            assertTrue("La sortie devrait contenir la fonction 'calculerSomme'", 
                    output.contains("calculerSomme"));
            assertTrue("La sortie devrait contenir la fonction 'afficherMessage'", 
                    output.contains("afficherMessage"));
            assertTrue("La sortie devrait contenir la variable locale 'i'", 
                    output.contains("i"));
            
            // Vérifier que les portées sont correctement affichées
            assertTrue("La sortie devrait contenir la portée globale", 
                    output.contains("global"));
            assertTrue("La sortie devrait contenir la portée locale", 
                    output.contains("global.loop"));
            
            // Vérifier que le formatage est correct
            assertTrue("Le formatage devrait inclure des sections pour les variables", 
                    output.contains("VARIABLES"));
            assertTrue("Le formatage devrait inclure des sections pour les fonctions", 
                    output.contains("FONCTIONS"));
            
            logger.info("Test d'affichage de la table des symboles réussi");
        } finally {
            // Restaurer System.out
            System.setOut(originalOut);
        }
    }
    
    // Note: Ce test a été commenté car il nécessite CompilerTestHelper qui n'est pas accessible
    // Pour tester avec un fichier réel EMJ, il faudrait étendre le test
    // en utilisant Main.main() directement
    /*
    @Test
    public void testSymbolTableWithEmojScript() throws Exception {
        // Ce test pourrait être implémenté autrement pour appeler directement le Main
        // Avec accès à la table des symboles après analyse
    }
    */
}
