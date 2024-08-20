from pysat.formula import CNF
from pysat.solvers import Solver

def encode_problem(tasks, resources):
    cnf = CNF()

    # Get the maximum time from the tasks' deadlines
    time = max(task[2] for task in tasks)

    # Variables x[i][j][t] for task i accessing resource j at time t
    x = [[[t + j*time + i*time*resources + 1 for t in range(time)] for j in range(resources)] for i in range(len(tasks))]

    # Initialize a variable counter
    var_counter = len(tasks) * resources * time + 1

    # Variables a[i][j][t] for start of non-preemptive access of resource j by task i at time t
    a = [[[var_counter + t + j*(time-tasks[i][1]+1) + i*(time-tasks[i][1]+1)*resources for t in range(time-tasks[i][1]+1)] for j in range(resources)] for i in range(len(tasks))]
    
    # Constraint A1: Task i should not access two resources at the same time
    for i in range(len(tasks)):
        for j in range(resources):
            for jp in range(j+1, resources):
                for t1 in range(time):
                    for t2 in range(time):
                        cnf.append([-x[i][j][t1], -x[i][jp][t2]])

    # Constraint A2: Each task must get some resource
    for i in range(len(tasks)):
        clause = []
        for j in range(resources):
            for t in range(time):
                clause.append(x[i][j][t])
        cnf.append(clause)

    # Constraint A3: A resource can only be held by one task at a time
    for i in range(len(tasks)):
        for ip in range(i+1, len(tasks)):
            for j in range(resources):
                for t in range(time):
                    cnf.append([-x[i][j][t], -x[ip][j][t]])

    # Constraint A4: Each task must have exactly one start time for accessing a resource non-preemptively
    for i in range(len(tasks)):
        clause = []
        for j in range(resources):
            for t in range(time - tasks[i][1] + 1):
                clause.append(a[i][j][t])
        cnf.append(clause)

    # Constraint A5: Linking start variable to x variables
    for i in range(len(tasks)):
        for j in range(resources):
            for t in range(time - tasks[i][1] + 1):
                # If a[i][j][t] is true, the task must hold the resource for its entire duration
                for tp in range(t, t + tasks[i][1]):
                    cnf.append([-a[i][j][t], x[i][j][tp]])

                # If a[i][j][t] is true, the task must not hold the resource before t
                for tp in range(0, t):
                    cnf.append([-a[i][j][t], -x[i][j][tp]])

                # If a[i][j][t] is true, the task must not hold the resource after t + e_i - 1
                for tp in range(t + tasks[i][1], time):
                    cnf.append([-a[i][j][t], -x[i][j][tp]])

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
