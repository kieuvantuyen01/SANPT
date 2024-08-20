from pysat.formula import CNF
from pysat.solvers import Solver

def encode_problem(tasks, resources):
    cnf = CNF()

    # Get the maximum time from the tasks' deadlines
    time = max(task[2] for task in tasks)

    # Initialize a variable counter
    var_counter = 1

    # Variables x[i][j][t] for task i accessing resource j at time t
    x = [[[var_counter + t + j*time + i*time*resources for t in range(time)] for j in range(resources)] for i in range(len(tasks))]

    # Update the variable counter
    var_counter += len(tasks) * resources * time

    # Variables a[i][j][t] for start of non-preemptive access of resource j by task i at time t
    a = [[[var_counter + t + j*time + i*time*resources for t in range(time)] for j in range(resources)] for i in range(len(tasks))]

    # Constraint A1
    for i in range(len(tasks)):
        for j in range(resources):
            for jp in range(j+1, resources):
                for t1 in range(time):
                    for t2 in range(time):
                        cnf.append([-x[i][j][t1], -x[i][jp][t2]])

    # Constraint A2
    for i in range(len(tasks)):
        clause = []
        for j in range(resources):
            for t in range(time):
                clause.append(x[i][j][t])
        cnf.append(clause)

    # Constraint A3
    for i in range(len(tasks)):
        for ip in range(i+1, len(tasks)):
            for j in range(resources):
                for t in range(time):
                    cnf.append([-x[i][j][t], -x[ip][j][t]])

    # Constraint A4
    for i in range(len(tasks)):
        clause = []
        for j in range(resources):
            for t in range(time):
                clause.append(a[i][j][t])
        cnf.append(clause)

    # Constraint A5
    for i in range(len(tasks)):
        for j in range(resources):
            for t in range(time):
                clause = [-a[i][j][t]]
                for tp in range(t):
                    clause.append(x[i][j][tp])
                cnf.append(clause)
                clause = [-a[i][j][t]]
                for tp in range(t+1, time):
                    clause.append(x[i][j][tp])
                cnf.append(clause)

    return cnf, time, x

# Use the encoding function with a SAT solver
tasks = [(0, 2, 2), (0, 2, 3)]  # Each task is a tuple (ri, ei, di)
resources = 2
cnf, time, x = encode_problem(tasks, resources)

with Solver(name="glucose4") as solver:
    solver.append_formula(cnf.clauses)
    result = solver.solve()
    if result:
        model = solver.get_model()
        for i in range(len(tasks)):
            for j in range(resources):
                for t in range(time):
                    if model[x[i][j][t]-1] > 0:
                        print(f"Task {i} is assigned to resource {j} at time {t}")
    else:
        print("No solution found")