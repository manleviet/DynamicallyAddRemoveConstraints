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
