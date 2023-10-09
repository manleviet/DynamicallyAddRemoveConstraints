/*
 * An example for dynamically add/remove constraints
 *
 * Copyright (c) 2023
 *
 * @author: Viet-Man Le (vietman.le@ist.tugraz.at)
 */

package at.tugraz.ist.ase;

import lombok.Builder;
import lombok.Data;
import org.chocosolver.solver.constraints.Constraint;

import java.util.List;

@Data
@Builder
public class ConstraintWrapper {
    private String name;
    private List<Constraint> constraints;
}
