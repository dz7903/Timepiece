﻿using Newtonsoft.Json;
using Timepiece;
using Timepiece.Angler;

ZenLib.ZenSettings.UseLargeStack = true;
ZenLib.ZenSettings.LargeStackSize = 30_000_000;

JsonSerializer Serializer()
{
  return new JsonSerializer
  {
    // use $type for type names, and the given binder
    TypeNameHandling = TypeNameHandling.All,
    SerializationBinder = RouteEnvironmentAst.Binder(),
    ContractResolver = RouteEnvironmentAst.Resolver(),
    // throw an error when members are missing from the object instead of ignoring them
    // MissingMemberHandling = MissingMemberHandling.Error
  };
}

foreach (var file in args)
{
  var json = new JsonTextReader(new StreamReader(file));
  var ast = Serializer().Deserialize<RouteEnvironmentAst>(json);
  Console.WriteLine($"Successfully deserialized JSON file {file}");
  json.Close();
  if (ast != null)
  {
    // ast.Validate();
    Profile.RunCmpPerNode(ast.ToNetwork());
  }
  else Console.WriteLine("Failed to deserialize contents of {file} (received null).");
}
