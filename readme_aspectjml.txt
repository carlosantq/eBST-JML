0. Download aspectjml-1.8.beta1.zip

1. Extract aspectjml-1.8.beta1.zip

2. Create Java Project in Eclipse

3. Create folder aspectjml-lib/ within the project

4. Copy \aspectjml-1.8.beta1\bin\aspectjml-release1.8.jar to the folder aspectjml-lib/

5. Copy all jar files within \aspectjml-1.8.beta1\aspectjml-lib to the folder aspectjml-lib/

6. Copy \aspectjml-1.8.beta1\ant_tasks\build.xml to the project root

7. Eclipse
    (Configuring Ant Task)
        - Window -> Show View -> Ant
        - Open Build.xml
        - Edit
            property name="main.class"           value="my.package.name.ClassnameOfMain"
          where my.package.name.ClassnameOfMain becomes your main class full name
        - Drag and Drop build.xml to the Ant View

    (ClassPath)
        - Adicione aspectjml-release1.8.jar e aspectjrt.jar ao build path do projeto

    (Compiling JML + Java)
        - Run ant task ajmlc [dafault]. This will erase the original bytecode and create an annotated bytecode
        - Run the main class
        - Every standard compilation (for instance, after editing and saving the main class) will overwrite the annotated bytecode. You need to run the ant task again to regenerated the annotated bytecode.
