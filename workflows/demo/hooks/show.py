def show(project):
    """One line per round: what is broken, what is unfinished, and the first of it."""
    grader = project["Grader"]
    errors, sorries = grader.get("errors"), grader.get("sorries")
    project.report.item(
        f"round {project.net.iterations}",
        f"{len(errors)} error(s), {len(sorries)} sorry(s) · "
        f"{errors[0] if errors else 'none'}")
