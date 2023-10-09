/*
 * An example for dynamically add/remove constraints
 *
 * Copyright (c) 2023
 *
 * @author: Viet-Man Le (vietman.le@ist.tugraz.at)
 */

package at.tugraz.ist.ase;

import com.google.common.base.Joiner;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import lombok.NonNull;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.variables.IntVar;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;

public class CarModel {

    public static String[] varNames = new String[] {"modell", "farbe", "motorisierung", "anwendung", "preisgruppe", "antriebsart"};
    public static IntVar[] vars;
    public static List<ConstraintWrapper> kb;
    public static List<ConstraintWrapper> restrictions;
    public static Model model;

    public static void createVariables() {
        // 1 - limousine , 2 - combi , 3 - suv, 4 - cabrio, 5 - van
        IntVar modell = model.intVar(varNames[0], new int[]{1, 2, 3, 4, 5});
        // 1 - schwarz , 2 - weib , 3 - grau, 4 - blau, 5 - rot
        IntVar farbe = model.intVar(varNames[1], new int[]{1, 2, 3, 4, 5});
        IntVar motorisierung = model.intVar(varNames[2], new int[]{100, 140, 180, 220, 260});
        // Other variables
        // 0 - pkw, 1 - transporter
        IntVar anwendung = model.intVar(varNames[3], new int[]{0, 1});
        // 0 - standard, 1 - preisklasse1, 2 - preisklasse2
        IntVar preisgruppe = model.intVar(varNames[4], new int[]{0, 1, 2});
        // 0 - benzin, 1 - diesel, 2 - elektrisch
        IntVar antriebsart = model.intVar(varNames[5], new int[]{0, 1, 2});

        vars = new IntVar[] {modell, farbe, motorisierung, anwendung, preisgruppe, antriebsart};
    }

    public static void createKB_Approach1() {
        // Constraints from the tables
        // Constraint c1: modell = limousine => anwendung = pkw
        // + using ifThen method to encode the imply operator. The
        //   ifThen method will be automatically posted.
        // + using arithm method to express the arithmetical constraints
        model.ifThen(
                model.arithm(vars[0],"=",1),
                model.arithm(vars[3],"=",0)
        );

        // Constraint c2: modell = combi => anwendung = transporter
        model.ifThen(
                model.arithm(vars[0],"=",2),
                model.arithm(vars[3],"=",1)
        );

        // Constraint c3: modell = suv => anwendung = pkw
        model.ifThen(
                model.arithm(vars[0],"=",3),
                model.arithm(vars[3],"=",0)
        );

        // Constraint c4: modell = cabrio => anwendung = pkw
        model.ifThen(
                model.arithm(vars[0],"=",4),
                model.arithm(vars[3],"=",0)
        );

        // Constraint c5: modell = van => anwendung = transporter
        model.ifThen(
                model.arithm(vars[0],"=",5),
                model.arithm(vars[3],"=",1)
        );

        // Constraint c6: farbe = schwarz => preisgruppe = standard
        model.ifThen(
                model.arithm(vars[1],"=",1),
                model.arithm(vars[4],"=",0)
        );

        // Constraint c7: farbe = weib => preisgruppe = preisklasse1
        model.ifThen(
                model.arithm(vars[1],"=",2),
                model.arithm(vars[4],"=",1)
        );

        // Constraint c8: farbe = grau => preisgruppe = preisklasse1
        model.ifThen(
                model.arithm(vars[1],"=",3),
                model.arithm(vars[4],"=",1)
        );

        // Constraint c9: farbe = blau => preisgruppe = preisklasse2
        model.ifThen(
                model.arithm(vars[1],"=",4),
                model.arithm(vars[4],"=",2)
        );

        // Constraint c10: farbe = rot => preisgruppe = preisklasse2
        model.ifThen(
                model.arithm(vars[1],"=",5),
                model.arithm(vars[4],"=",2)
        );

        // Constraint c11: motorisierung = 100 => antriebsart = benzin
        model.ifThen(
                model.arithm(vars[2],"=",100),
                model.arithm(vars[5],"=",0)
        );

        // Constraint c12: motorisierung = 140 => antriebsart = diesel
        model.ifThen(
                model.arithm(vars[2],"=",140),
                model.arithm(vars[5],"=",1)
        );

        // Constraint c13: motorisierung = 180 => antriebsart = diesel
        model.ifThen(
                model.arithm(vars[2],"=",180),
                model.arithm(vars[5],"=",1)
        );

        // Constraint c14: motorisierung = 220 => antriebsart = benzin
        model.ifThen(
                model.arithm(vars[2],"=",220),
                model.arithm(vars[5],"=",0)
        );

        // Constraint c15: motorisierung = 260 => antriebsart = elektrisch
        model.ifThen(
                model.arithm(vars[2],"=",260),
                model.arithm(vars[5],"=",2)
        );

        // Restrictions
        // Constraint c16: Diesel Limousine does not come in blue and gray
        // modell = limousine /\ antriebsart = diesel => farbe != blau /\ farbe != grau
        model.ifThen(
                model.and(model.arithm(vars[0],"=",1),
                        model.arithm(vars[5],"=",1)),
                model.and(model.arithm(vars[1],"!=",3),
                        model.arithm(vars[1],"!=",4))
        );
        // Constraint c17: Benzin Limousine does not exist in price class1
        // modell = limousine /\ antriebsart = benzin => preisgruppe != preisklasse1
        model.ifThen(
                model.and(model.arithm(vars[0],"=",1),
                        model.arithm(vars[5],"=",0)),
                model.arithm(vars[4],"!=",1)
        );
        // Constraint c18: Transporter is only available in electric or diesel version
        // anwendung = transporter => antriebsart = elektrisch \/ antriebsart = diesel
        // anwendung = transporter => antriebsart != benzin
        model.ifThen(
                model.arithm(vars[3],"=",1),
                model.arithm(vars[5],"!=",0)
        );
        // Constraint c19: Cabrios are not available in Standard colors and only as Diesel and Benzin models.
        // modell = cabrio => preisgruppe != standard
        model.ifThen(
                model.arithm(vars[0],"=",4),
                model.arithm(vars[4],"!=",0)
        );
        // Constraint c20: But the Red Carbio is also available electrically
        // modell = cabrio /\ farbe = rot => antriebsart = elektrisch
        model.ifThen(
                model.and(model.arithm(vars[0],"=",4),
                        model.arithm(vars[1],"=",5)),
                model.arithm(vars[5],"=",2)
        );
        // modell = cabrio /\ farbe != rot => antriebsart != elektrisch
        model.ifThen(
                model.and(model.arithm(vars[0],"=",4),
                        model.arithm(vars[1],"!=",5)),
                model.arithm(vars[5],"!=",2)
        );
    }

    public static List<Constraint> getConstraints(@NonNull Model model, int startIdx, int endIdx) {
        Constraint[] cstrs = model.getCstrs();

        checkElementIndex(startIdx, cstrs.length, "startIdx must be within the range of constraints");
        checkElementIndex(endIdx, cstrs.length, "endIdx must be within the range of constraints");
        checkArgument(startIdx <= endIdx, "startIdx must be <= endIdx");

        List<Constraint> constraints = new LinkedList<>();
        int index = startIdx;
        while (index <= endIdx) {
            constraints.add(cstrs[index]);

            index++;
        }
        return constraints;
    }

    public static void createKB_Approach2() {
        kb = new ArrayList<>();
        restrictions = new ArrayList<>();

        // Constraints from the tables
        // Constraint c1: modell = limousine => anwendung = pkw
        // + using ifThen method to encode the imply operator. The
        //   ifThen method will be automatically posted.
        // + using arithm method to express the arithmetical constraints
        int counter = 0;
        model.ifThen(
                model.arithm(vars[0],"=",1),
                model.arithm(vars[3],"=",0)
        );
        // add Choco constraints to ConstraintWrapper
        List<Constraint> cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c1 = ConstraintWrapper.builder()
                .name("modell = limousine => anwendung = pkw")
                .constraints(cstrs)
                .build();
        kb.add(c1);

        // Constraint c2: modell = combi => anwendung = transporter
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[0],"=",2),
                model.arithm(vars[3],"=",1)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c2 = ConstraintWrapper.builder()
                .name("modell = combi => anwendung = transporter")
                .constraints(cstrs)
                .build();
        kb.add(c2);

        // Constraint c3: modell = suv => anwendung = pkw
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[0],"=",3),
                model.arithm(vars[3],"=",0)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c3 = ConstraintWrapper.builder()
                .name("modell = suv => anwendung = pkw")
                .constraints(cstrs)
                .build();
        kb.add(c3);

        // Constraint c4: modell = cabrio => anwendung = pkw
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[0],"=",4),
                model.arithm(vars[3],"=",0)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c4 = ConstraintWrapper.builder()
                .name("modell = cabrio => anwendung = pkw")
                .constraints(cstrs)
                .build();
        kb.add(c4);

        // Constraint c5: modell = van => anwendung = transporter
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[0],"=",5),
                model.arithm(vars[3],"=",1)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c5 = ConstraintWrapper.builder()
                .name("modell = van => anwendung = transporter")
                .constraints(cstrs)
                .build();
        kb.add(c5);

        // Constraint c6: farbe = schwarz => preisgruppe = standard
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[1],"=",1),
                model.arithm(vars[4],"=",0)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c6 = ConstraintWrapper.builder()
                .name("farbe = schwarz => preisgruppe = standard")
                .constraints(cstrs)
                .build();
        kb.add(c6);

        // Constraint c7: farbe = weib => preisgruppe = preisklasse1
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[1],"=",2),
                model.arithm(vars[4],"=",1)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c7 = ConstraintWrapper.builder()
                .name("farbe = weib => preisgruppe = preisklasse1")
                .constraints(cstrs)
                .build();
        kb.add(c7);

        // Constraint c8: farbe = grau => preisgruppe = preisklasse1
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[1],"=",3),
                model.arithm(vars[4],"=",1)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c8 = ConstraintWrapper.builder()
                .name("farbe = grau => preisgruppe = preisklasse1")
                .constraints(cstrs)
                .build();
        kb.add(c8);

        // Constraint c9: farbe = blau => preisgruppe = preisklasse2
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[1],"=",4),
                model.arithm(vars[4],"=",2)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c9 = ConstraintWrapper.builder()
                .name("farbe = blau => preisgruppe = preisklasse2")
                .constraints(cstrs)
                .build();
        kb.add(c9);

        // Constraint c10: farbe = rot => preisgruppe = preisklasse2
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[1],"=",5),
                model.arithm(vars[4],"=",2)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c10 = ConstraintWrapper.builder()
                .name("farbe = rot => preisgruppe = preisklasse2")
                .constraints(cstrs)
                .build();
        kb.add(c10);

        // Constraint c11: motorisierung = 100 => antriebsart = benzin
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[2],"=",100),
                model.arithm(vars[5],"=",0)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c11 = ConstraintWrapper.builder()
                .name("motorisierung = 100 => antriebsart = benzin")
                .constraints(cstrs)
                .build();
        kb.add(c11);

        // Constraint c12: motorisierung = 140 => antriebsart = diesel
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[2],"=",140),
                model.arithm(vars[5],"=",1)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c12 = ConstraintWrapper.builder()
             .name("motorisierung = 140 => antriebsart = diesel")
             .constraints(cstrs)
             .build();
        kb.add(c12);

        // Constraint c13: motorisierung = 180 => antriebsart = diesel
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[2],"=",180),
                model.arithm(vars[5],"=",1)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c13 = ConstraintWrapper.builder()
                .name("motorisierung = 180 => antriebsart = diesel")
                .constraints(cstrs)
                .build();
        kb.add(c13);

        // Constraint c14: motorisierung = 220 => antriebsart = benzin
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[2],"=",220),
                model.arithm(vars[5],"=",0)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c14 = ConstraintWrapper.builder()
                .name("motorisierung = 220 => antriebsart = benzin")
                .constraints(cstrs)
                .build();
        kb.add(c14);

        // Constraint c15: motorisierung = 260 => antriebsart = elektrisch
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[2],"=",260),
                model.arithm(vars[5],"=",2)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c15 = ConstraintWrapper.builder()
                .name("motorisierung = 260 => antriebsart = elektrisch")
                .constraints(cstrs)
                .build();
        kb.add(c15);

        // Restrictions
        // Constraint c16: Diesel Limousine does not come in blue and gray
        // modell = limousine /\ antriebsart = diesel => farbe != blau /\ farbe != grau
        counter = model.getNbCstrs();
        model.ifThen(
                model.and(model.arithm(vars[0],"=",1),
                        model.arithm(vars[5],"=",1)),
                model.and(model.arithm(vars[1],"!=",3),
                        model.arithm(vars[1],"!=",4))
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c16 = ConstraintWrapper.builder()
                .name("Diesel Limousine does not come in blue and gray")
                .constraints(cstrs)
                .build();
        restrictions.add(c16);

        // Constraint c17: Benzin Limousine does not exist in price class1
        // modell = limousine /\ antriebsart = benzin => preisgruppe != preisklasse1
        counter = model.getNbCstrs();
        model.ifThen(
                model.and(model.arithm(vars[0],"=",1),
                        model.arithm(vars[5],"=",0)),
                model.arithm(vars[4],"!=",1)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c17 = ConstraintWrapper.builder()
                .name("Benzin Limousine does not exist in price class1")
                .constraints(cstrs)
                .build();
        restrictions.add(c17);

        // Constraint c18: Transporter is only available in electric or diesel version
        // anwendung = transporter => antriebsart = elektrisch \/ antriebsart = diesel
        // anwendung = transporter => antriebsart != benzin
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[3],"=",1),
                model.arithm(vars[5],"!=",0)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c18 = ConstraintWrapper.builder()
                .name("Transporter is only available in electric or diesel version")
                .constraints(cstrs)
                .build();
        restrictions.add(c18);

        // Constraint c19: Cabrios are not available in Standard colors and only as Diesel and Benzin models.
        // modell = cabrio => preisgruppe != standard
        counter = model.getNbCstrs();
        model.ifThen(
                model.arithm(vars[0],"=",4),
                model.arithm(vars[4],"!=",0)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c19 = ConstraintWrapper.builder()
                .name("Cabrios are not available in Standard colors and only as Diesel and Benzin models.")
                .constraints(cstrs)
                .build();
        restrictions.add(c19);

        // Constraint c20: But the Red Carbio is also available electrically
        // modell = cabrio /\ farbe = rot => antriebsart = elektrisch
        counter = model.getNbCstrs();
        model.ifThen(
                model.and(model.arithm(vars[0],"=",4),
                        model.arithm(vars[1],"=",5)),
                model.arithm(vars[5],"=",2)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c20 = ConstraintWrapper.builder()
                .name("But the Red Carbio is also available electrically")
                .constraints(cstrs)
                .build();
        restrictions.add(c20);

        // modell = cabrio /\ farbe != rot => antriebsart != elektrisch
        counter = model.getNbCstrs();
        model.ifThen(
                model.and(model.arithm(vars[0],"=",4),
                        model.arithm(vars[1],"!=",5)),
                model.arithm(vars[5],"!=",2)
        );
        // add Choco constraints to ConstraintWrapper
        cstrs = getConstraints(model, counter, model.getNbCstrs() - 1);
        ConstraintWrapper c21 = ConstraintWrapper.builder()
                .name("modell = cabrio /\\ farbe != rot => antriebsart != elektrisch")
                .constraints(cstrs)
                .build();
        restrictions.add(c21);
    }

    /**
     * Approach 1 - using the environment
     * Relevant for the scenario where we add/remove user requirements
     */
    public static void approach1() {
        model = new Model("Combeenation Car Model");

        // Decision variables
        createVariables();

        // Knowledge Base
        createKB_Approach1();

//        System.out.println(model.getNbCstrs());

//        for (Constraint c: model.getCstrs()) {
//            System.out.println(c);
//        }

        // First user requirement: Limousine
        model.arithm(vars[0],"=",1).post();

        System.out.println();
        System.out.println("------ First, User selects LIMOUSINE ------");
        solve_Approach1(model);

        // Second user requirement: 140 kW (diesel)
        model.arithm(vars[2],"=",140).post();

        System.out.println();
        System.out.println("------ Second, User selects 140 kW motor (Diesel) ------");
        solve_Approach1(model);
    }

    /**
     * Approach 2 - post and unpost constraints
     * Relevant for the scenario where we add/remove constraints of kb
     */
    public static void approach2() {
        model = new Model("Combeenation Car Model");

        // Decision variables
        createVariables();

        // Knowledge Base
        createKB_Approach2();

        // remove/unpost all created constraints
        model.unpost(model.getCstrs());

//        System.out.println(model.getNbCstrs());

//        for (Constraint c: model.getCstrs()) {
//            System.out.println(c);
//        }

        // Find all solutions for the initial model
        System.out.println();
        System.out.println("------ Find all solutions for the initial model ------");
        Iterable<ConstraintWrapper> combinedIterables = Iterables.unmodifiableIterable(Iterables.concat(kb, restrictions));
        solve_Approach2(model, Lists.newArrayList(combinedIterables));

        // Find all solutions for the model without restrictions (without c16, c17, c18, c19, c20, c21)

        System.out.println();
        System.out.println("------ Find all solutions for the model without restrictions (without c16, c17, c18, c19, c20, c21) ------");
        solve_Approach2(model, kb);
    }

    public static void main(String[] args) {
        System.out.println("------ APPROACH 1 ------");
        approach1();

        System.out.println();
        System.out.println("------ APPROACH 2 ------");
        approach2();
    }

    /**
     * Approach 1 - using the environment
     */
    public static void solve_Approach1(Model model) {
        // get the Solver object from the Model object
        Solver solver = model.getSolver();
        // save the original model
        model.getEnvironment().worldPush();

        solve(solver, -1);

        // get back the original model
        model.getEnvironment().worldPop();
        model.getSolver().reset();
    }

    /**
     * Approach 2 - post and unpost constraints
     */
    public static void solve_Approach2(Model model, List<ConstraintWrapper> constraints) {
        // get the Solver object from the Model object
        Solver solver = model.getSolver();

        // post constraints
        constraints.stream().map(c -> c.getConstraints().toArray(new Constraint[0])).forEach(model::post);

        solve(solver, 10);

        // unpost all constraints
        model.unpost(model.getCstrs());
        model.getSolver().reset(); // reset the solver
    }

    private static void solve(Solver solver, int maxSolutions) {
        AtomicInteger solutionCounter = new AtomicInteger();
        while (solver.solve()) {
            solutionCounter.getAndIncrement();

            System.out.println("Solution " + solutionCounter.get() + ":");

            printSolution();

            if (maxSolutions != -1 && solutionCounter.get() == maxSolutions) {
                break;
            }
        }

        if (solutionCounter.get() == 0) {
            System.out.println("No solution found.");
        } else {
            System.out.println("Total solutions: " + solutionCounter.get());
        }
    }

    private static void printSolution() {
        String solutions = Joiner.on(",")
                .join(Arrays.stream(vars)
                        .map(var -> var.getName() + " = " + getRealValue(var.getName(), var.getValue()))
                        .toArray());
        System.out.println(solutions);
    }

    private static String getRealValue(String varName, int value) {
        return switch (varName) {
            case "modell" -> getRealValueForModell(value);
            case "farbe" -> getRealValueForFarbe(value);
            case "motorisierung" -> getRealValueForMotorisierung(value);
            case "anwendung" -> getRealValueForAnwendung(value);
            case "preisgruppe" -> getRealValueForPreisgruppe(value);
            case "antriebsart" -> getRealValueForAntriebsart(value);
            default -> "";
        };
    }

    private static String getRealValueForAntriebsart(int value) {
        // 0 - benzin, 1 - diesel, 2 - elektrisch
        return switch (value) {
            case 0 -> "benzin";
            case 1 -> "diesel";
            case 2 -> "elektrisch";
            default -> "";
        };
    }

    private static String getRealValueForPreisgruppe(int value) {
        // 0 - standard, 1 - preisklasse1, 2 - preisklasse2
        return switch (value) {
            case 0 -> "standard";
            case 1 -> "preisklasse1";
            case 2 -> "preisklasse2";
            default -> "";
        };
    }

    private static String getRealValueForAnwendung(int value) {
        // 0 - pkw, 1 - transporter
        return switch (value) {
            case 0 -> "pkw";
            case 1 -> "transporter";
            default -> "";
        };
    }

    private static String getRealValueForModell(int value) {
        // 1 - limousine , 2 - combi , 3 - suv, 4 - cabrio, 5 - van
        return switch (value) {
            case 1 -> "limousine";
            case 2 -> "combi";
            case 3 -> "suv";
            case 4 -> "cabrio";
            case 5 -> "van";
            default -> "";
        };
    }

    private static String getRealValueForFarbe(int value) {
        // 1 - schwarz , 2 - weib , 3 - grau, 4 - blau, 5 - rot
        return switch (value) {
            case 1 -> "schwarz";
            case 2 -> "weib";
            case 3 -> "grau";
            case 4 -> "blau";
            case 5 -> "rot";
            default -> "";
        };
    }

    private static String getRealValueForMotorisierung(int value) {
        // 100, 140, 180, 220, 260
        return "" + value + " kW";
    }
}