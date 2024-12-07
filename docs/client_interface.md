# CStar Client Interface
## Structure
See [README.md](../README.md)

## package.json
- configuration: initializationOptions settings
- commands
- keybindings
- menus

## client/src/extension.ts

### sendRquest of a Capability
- nothing to change

### sendNotification
- extension.ts: sendNotification("Same as CStar Server ExtProtocol.Client_", params) 

### onNotification
- types.ts: YOUR_TYPE
- extension.ts: onNotification("Same as CStar Server ExtProtocol.Server_", (params)=>{}) 

## client/src/types.ts
- YOUR_TYPE

## Reference
- [Development strategy](https://blog.haoji.me/vscode-plugin-overview.html)
- [vscode extension repo](https://github.com/microsoft/vscode-extension-samples/tree/main)
- [visualstudio](https://code.visualstudio.com/api/ux-guidelines/overview)

# Run
npm run compile

# Publish
- version
- vsce package
- vsce publish